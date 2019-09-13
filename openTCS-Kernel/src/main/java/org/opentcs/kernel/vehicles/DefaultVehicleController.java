/**
 * Copyright (c) The openTCS Authors.
 * <p>
 * This program is free software and subject to the MIT license. (For details,
 * see the licensing information (LICENSE.txt) you should have received with
 * this copy of the software.)
 */
package org.opentcs.kernel.vehicles;

import com.google.common.util.concurrent.Uninterruptibles;
import com.google.inject.assistedinject.Assisted;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.*;

import static java.util.Objects.isNull;
import static java.util.Objects.requireNonNull;

import java.util.concurrent.TimeUnit;
import java.util.regex.Pattern;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.inject.Inject;

import org.jgrapht.Graph;
import org.jgrapht.alg.shortestpath.DijkstraShortestPath;
import org.opentcs.access.LocalKernel;
import org.opentcs.access.to.order.DestinationCreationTO;
import org.opentcs.access.to.order.TransportOrderCreationTO;
import org.opentcs.components.kernel.ResourceAllocationException;
import org.opentcs.components.kernel.Scheduler;
import org.opentcs.components.kernel.services.*;
import org.opentcs.customizations.ApplicationEventBus;
import org.opentcs.data.ObjectUnknownException;
import org.opentcs.data.TCSObjectEvent;
import org.opentcs.data.TCSObjectReference;
import org.opentcs.data.model.*;
import org.opentcs.data.notification.UserNotification;
import org.opentcs.data.order.DriveOrder;
import org.opentcs.data.order.Route;
import org.opentcs.data.order.Route.Step;
import org.opentcs.data.order.TransportOrder;
import org.opentcs.drivers.vehicle.AdapterCommand;
import org.opentcs.drivers.vehicle.LoadHandlingDevice;
import org.opentcs.drivers.vehicle.MovementCommand;
import org.opentcs.drivers.vehicle.VehicleCommAdapter;
import org.opentcs.drivers.vehicle.VehicleCommAdapterEvent;
import org.opentcs.drivers.vehicle.VehicleController;
import org.opentcs.drivers.vehicle.VehicleProcessModel;
import org.opentcs.drivers.vehicle.management.ProcessModelEvent;

import static org.opentcs.util.Assertions.checkArgument;
import static org.opentcs.util.Assertions.checkState;

import org.opentcs.kernel.services.StandardPlantModelService;
import org.opentcs.kernel.workingset.Model;
import org.opentcs.kernel.workingset.TCSObjectPool;
import org.opentcs.strategies.basic.dispatching.RerouteUtil;
import org.opentcs.strategies.basic.dispatching.TransportOrderUtil;
import org.opentcs.strategies.basic.routing.PointRouter;
import org.opentcs.strategies.basic.routing.jgrapht.ModelEdge;
import org.opentcs.strategies.basic.routing.jgrapht.ModelGraphMapper;
import org.opentcs.strategies.basic.routing.jgrapht.ShortestPathPointRouter;
import org.opentcs.util.ExplainedBoolean;
import org.opentcs.util.event.EventBus;
import org.opentcs.util.event.EventHandler;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Realizes a bidirectional connection between the kernel and a communication adapter controlling a
 * vehicle.
 *
 * @author Stefan Walter (Fraunhofer IML)
 */
public class DefaultVehicleController
        implements VehicleController,
        PropertyChangeListener,
        EventHandler {

  /**
   * This class's Logger.
   */
  private static final Logger LOG = LoggerFactory.getLogger(DefaultVehicleController.class);
  /**
   * The local kernel.
   */
  private final LocalKernel localKernel;
  /**
   * The kernel's vehicle service.
   */
  private final InternalVehicleService vehicleService;
  /**
   * The kernel's notification service.
   */
  private final NotificationService notificationService;
  /**
   * The kernel's dispatcher service.
   */
  private final DispatcherService dispatcherService;
  /**
   * The scheduler maintaining the resources.
   */
  private final Scheduler scheduler;
  /**
   * The event bus we should register with and send events to.
   */
  private final EventBus eventBus;
  /**
   * The vehicle controlled by this controller/the communication adapter.
   */
  private final Vehicle vehicle;
  /**
   * The communication adapter controlling the physical vehicle.
   */
  private final VehicleCommAdapter commAdapter;
  /**
   * This controller's <em>enabled</em> flag.
   */
  private volatile boolean initialized;
  /**
   * A list of commands that still need to be sent to the communication adapter.
   */
  private final Queue<MovementCommand> futureCommands = new LinkedList<>();
  /**
   * A command for which a resource allocation is pending and which has not yet been sent to the
   * adapter.
   */
  private volatile MovementCommand pendingCommand;
  /**
   * A set of resources for which allocation is pending.
   */
  private volatile Set<TCSResource<?>> pendingResources;
  /**
   * A list of commands that have been sent to the communication adapter.
   */
  private final Queue<MovementCommand> commandsSent = new LinkedList<>();
  /**
   * The last command that has been executed.
   */
  private MovementCommand lastCommandExecuted;
  /**
   * The resources this controller has allocated for each command.
   */
  private final Queue<Set<TCSResource<?>>> allocatedResources = new LinkedList<>();
  /**
   * The drive order that the vehicle currently has to process.
   */
  private volatile DriveOrder currentDriveOrder;
  /**
   * The communication adapter's last known state.
   */
  @SuppressWarnings("deprecation")
  private volatile VehicleCommAdapter.State commAdapterState = VehicleCommAdapter.State.UNKNOWN;
  /**
   * Flag indicating that we're currently waiting for resources to be allocated
   * by the scheduler, ensuring that we do not allocate more than one set of
   * resources at a time (which can cause deadlocks).
   */
  private volatile boolean waitingForAllocation;

  @Inject
  private TCSObjectPool objectPool;
  @Inject
  private PlantModelService plantModelService;
  @Inject
  private ModelGraphMapper mapper;
  @Inject
  private RouterService routerService;
  @Inject
  private TransportOrderUtil transportOrderUtil;
  @Inject
  private TransportOrderService transportOrderService;
  @Inject
  private RerouteUtil rerouteUtil;
  private Thread checkVehicleStateThread;
  private int tryLockFailCount = 0;
  private boolean isCleared = false;
  private Graph<String, ModelEdge> graph;
  private Set<Path> paths;

  synchronized public void setCleared(boolean cleared) {
    isCleared = cleared;
  }

  /**
   * Creates a new instance associated with the given vehicle.
   *
   * @param vehicle             The vehicle this vehicle controller will be associated with.
   * @param adapter             The communication adapter of the associated vehicle.
   * @param kernel              The kernel instance maintaining the model.
   * @param vehicleService      The kernel's vehicle service.
   * @param notificationService The kernel's notification service.
   * @param dispatcherService   The kernel's dispatcher service.
   * @param scheduler           The scheduler managing resource allocations.
   * @param eventBus            The event bus this instance should register with and send events to.
   */
  @Inject
  public DefaultVehicleController(@Assisted @Nonnull Vehicle vehicle,
                                  @Assisted @Nonnull VehicleCommAdapter adapter,
                                  @Nonnull LocalKernel kernel,
                                  @Nonnull InternalVehicleService vehicleService,
                                  @Nonnull NotificationService notificationService,
                                  @Nonnull DispatcherService dispatcherService,
                                  @Nonnull Scheduler scheduler,
                                  @Nonnull @ApplicationEventBus EventBus eventBus) {
    this.vehicle = requireNonNull(vehicle, "vehicle");
    this.commAdapter = requireNonNull(adapter, "adapter");
    this.localKernel = requireNonNull(kernel, "kernel");
    this.vehicleService = requireNonNull(vehicleService, "vehicleService");
    this.notificationService = requireNonNull(notificationService, "notificationService");
    this.dispatcherService = requireNonNull(dispatcherService, "dispatcherService");
    this.scheduler = requireNonNull(scheduler, "scheduler");
    this.eventBus = requireNonNull(eventBus, "eventBus");
  }

  @Override
  public boolean isInitialized() {
    return initialized;
  }

  @Override
  @SuppressWarnings("deprecation")
  public void initialize() {
    if (isInitialized()) {
      return;
    }

    eventBus.subscribe(this);

    vehicleService.updateVehicleRechargeOperation(vehicle.getReference(),
            commAdapter.getRechargeOperation());
    commAdapter.getProcessModel().addPropertyChangeListener(this);

    // Initialize standard attributes once.
    setVehiclePosition(commAdapter.getProcessModel().getVehiclePosition());
    vehicleService.updateVehiclePrecisePosition(
            vehicle.getReference(),
            commAdapter.getProcessModel().getVehiclePrecisePosition()
    );
    vehicleService.updateVehicleOrientationAngle(
            vehicle.getReference(),
            commAdapter.getProcessModel().getVehicleOrientationAngle()
    );
    vehicleService.updateVehicleEnergyLevel(vehicle.getReference(),
            commAdapter.getProcessModel().getVehicleEnergyLevel());
    vehicleService.updateVehicleLoadHandlingDevices(
            vehicle.getReference(),
            commAdapter.getProcessModel().getVehicleLoadHandlingDevices()
    );
    updateVehicleState(commAdapter.getProcessModel().getVehicleState());
    updateCommAdapterState(commAdapter.getProcessModel().getVehicleAdapterState());

    // Add a first entry into allocatedResources to shift freeing of resources
    // in commandExecuted() by one - we need to free the resources allocated for
    // the command before the one executed there.
    allocatedResources.add(null);

    initVehicleStateListener();

    initialized = true;
  }

  private void initVehicleStateListener() {
    // 0910 start
    StandardPlantModelService plantModelService = (StandardPlantModelService) this.plantModelService;

    // get whole model in kernel
//    Model model = plantModelService.getModel();
//    Pattern compile = Pattern.compile(".*");
//    paths = model.getPaths(compile);
//    Set<Point> points = model.getPoints(compile);

    //get jGrapht shortestPath router
//    graph = mapper.translateModel(points, paths, vehicle);
//    PointRouter router = new ShortestPathPointRouter(new DijkstraShortestPath<>(graph), points);

//    Point pre = null;
//    for (Point point : points) {
//      if (pre != null) {
//        List<Step> routeSteps = router.getRouteSteps(pre, point);
//        StringBuilder sb = new StringBuilder();
//        for (Step step : routeSteps) {
//          sb.append(step.getSourcePoint().getName() + " -> " + step.getDestinationPoint().getName() + ", ");
//        }
//        LOG.warn(sb.toString());
//      }
//      LOG.warn(point.getName());
//      pre = point;
//    }

//    for (Path path : paths) {
//      LOG.warn(path.getName());
//    }

//    AtomicBoolean flag = new AtomicBoolean(true);
//    Map<String, String> sharedMap = objectPool.getSharedMap();
    checkVehicleStateThread = new Thread(() -> {
      while (true) {
        // update sharedMap
//        VehicleProcessModel processModel = commAdapter.getProcessModel();
//        String name = processModel.getVehicle().getName();
//        String position = processModel.getVehiclePosition();
//        LOG.warn(name + "[" + position + "]");
//        for (String s : sharedMap.keySet()) {
//          LOG.warn("<" + s + ", " + sharedMap.get(s) + ">");
//        }

        // check next path and try lock nextStep, if curStep is final step, do nothing.
        if (currentDriveOrder != null) {
          // 请求下一步的锁
          if (futureCommands.size() > 0) {
            Step nextStep = futureCommands.peek().getStep();
            lockNextStep(nextStep);
          }

          // 释放上一步的锁
          ArrayList<MovementCommand> lastCommandSent = new ArrayList<>(commandsSent);
          List<Step> allSteps = currentDriveOrder.getRoute().getSteps();
          if (lastCommandSent.size() == 1 && lastCommandSent.get(0).getStep().getRouteIndex() > 0) {
            Step lastStep = allSteps.get(lastCommandSent.get(0).getStep().getRouteIndex() - 1);
            unLockStep(lastStep);
          } else if (lastCommandSent.size() == 0) {
            // 等待资源暂停中，lastCommandSent已被执行，但是futureCommands还有未执行的
//            LOG.warn("lastCommandSent size is zero, futureCommands size is " + futureCommands.size());
          }

//          LOG.warn("All we know is : "
//                  + vehicle.getName() + ", "
//                  + currentDriveOrder.toString() + ", "
//                  + commandsSent.size() + ", "
//                  + futureCommands.size());
//          StringBuilder sb = new StringBuilder();
//          List<Step> steps = currentDriveOrder.getRoute().getSteps();
//          for (Step step : steps) {
//            sb.append(step.getPath().getSourcePoint().getName() + "->" + step.getPath().getDestinationPoint().getName());
//            sb.append(", ");
//          }
//          LOG.warn(sb.toString());
          // if necessary:
          // update driveOrder
//      updateDriveOrder(null, null);
          // sentCommand

//          if (flag.get()) {

          //detect conflict and 1.abort 2.reroute
//            Uninterruptibles.sleepUninterruptibly(5000, TimeUnit.MILLISECONDS);
//            Path nextPath = futureCommands.peek().getStep().getPath();
//            TCSResourceReference<Path> nextPathRef = nextPath.getReference();


//          LOG.warn("Abort now, nextPath to be locked is : " + nextPath.getName());
//          dispatcherService.withdrawByVehicle(vehicle.getReference(), true, false);

//            LOG.warn("Pause now, from point : " + nextPath.getSourcePoint().getName());
//            futureCommands.peek().getStep().setExecutionAllowed(false);

//            Uninterruptibles.sleepUninterruptibly(15000, TimeUnit.MILLISECONDS);
//            LOG.warn("LockPath now, from point : " + nextPath.getSourcePoint().getName());
//            routerService.updatePathLock(nextPathRef, true);
//            Uninterruptibles.sleepUninterruptibly(5000, TimeUnit.MILLISECONDS);
//            LOG.warn("UnLockPath now, from point : " + nextPath.getSourcePoint().getName());
//            routerService.updatePathLock(nextPathRef, false);
//            flag.set(false);
//          }


//      sendCommAdapterCommand(null);
          // abort order
//          Uninterruptibles.sleepUninterruptibly(3000, TimeUnit.MILLISECONDS);
//          abortDriveOrder();
//          sendCommAdapterCommand();  // xxxCommand.execute is changing processModel directly，not good.
        } else {
          // 起点与终点相同的transportOrder（压根进不来，直接成功）
          if (commAdapter.getProcessModel().getVehicle().getTransportOrder() != null) {
            LOG.warn("Although curOrder is null, but transportOrder is : " + commAdapter.getProcessModel().getVehicle().getTransportOrder().getName());
          }
          if (!isCleared && commAdapter.getProcessModel().getVehiclePosition() != null) {
            //curOrder 已全部执行完，清理最后一步的锁
            LOG.warn("ClearLocks when curOrder is null.");
            clearLocksExcept(commAdapter.getProcessModel().getVehiclePosition());
            setCleared(true);

            // 如果是第一次设置小车初始位置，则这个位置强制加锁（即便这个地方有别的车正在请求或者已请求到了锁）
            LOG.warn("Lock curPosition when curOrder is null anyway.");
            objectPool.getSharedLockInformation().put(commAdapter.getProcessModel().getVehiclePosition(), vehicle.getName());
          }
        }
        Uninterruptibles.sleepUninterruptibly(500, TimeUnit.MILLISECONDS);
      }
    }, "BDKELoopThread-" + vehicle.getName());
    checkVehicleStateThread.start();
    // 0910 end
  }

  private void unLockStep(Step s) {
    String sourcePointName = s.getSourcePoint().getName();
    // 如果小车是原路返回，则不能解锁这一步，
    // 换句话说，要解锁的不能是接下来的两步（接下来的2步必须保持锁定）
    if (futureCommands.peek() != null &&
            (futureCommands.peek().getStep().getSourcePoint().getName().equals(sourcePointName) ||
                    futureCommands.peek().getStep().getDestinationPoint().getName().equals(sourcePointName))) {
      LOG.warn("Go back way, so not unlock " + sourcePointName + " which it will pass in two future steps.");
      return;
    }

    if (objectPool.getSharedLockInformation().containsKey(sourcePointName)
            && objectPool.getSharedLockInformation().get(sourcePointName).equals(vehicle.getName())) {
      objectPool.getSharedLockInformation().remove(sourcePointName);
      LOG.warn("Remove point lock : " + sourcePointName);
    }
  }

  private void lockNextStep(Step nextStep) {
    LOG.warn("Try to lock point : " + nextStep.getPath().getDestinationPoint().getName());
    if (!tryLockStep(nextStep)) {

      if (nextStep.isExecutionAllowed()) {
        nextStep.setExecutionAllowed(false);  // pause 不合适，当前命令必须立即停止，发一个命令让小车立即停止。
      }
//            abortDriveOrder();

      tryLockFailCount++;
      LOG.warn("Lock fail for point " + nextStep.getPath().getDestinationPoint().getName() + " in [" + tryLockFailCount + "] times.");
      if (tryLockFailCount >= 100) {
        //100次失败后重新规划路径
        //为了将来能够手动/自动恢复拓扑图做准备
        Map<String, List<TCSObjectReference<Path>>> map = objectPool.getSharedTopologyInformation();
        if (map.get(nextStep.getDestinationPoint().getName()) != null) {
          map.get(nextStep.getDestinationPoint().getName()).add(nextStep.getPath().getReference());
        } else {
          ArrayList<TCSObjectReference<Path>> list = new ArrayList<>();
          list.add(nextStep.getPath().getReference());
          map.put(nextStep.getDestinationPoint().getName(), list);
        }
        reRoute(nextStep);
        LOG.warn("Already tried " + tryLockFailCount + " times, reroute for current vehicle because path " + nextStep.getPath().getName() + " is disabled.");
        tryLockFailCount = 0;

        // 容错
        // 有一种情况会导致修改的拓扑无法改回来（即快请求100次的时候，占用该点的小车走了，等到了100次，会改变该点拓扑，由于小车已经走了，因此没有谁能触发该点的恢复）
        new Thread(() -> {
          Uninterruptibles.sleepUninterruptibly(3000, TimeUnit.MILLISECONDS);
          recoveryTopology(nextStep.getDestinationPoint().getName());
          LOG.warn("3s later we recoveryTopology change from point " + nextStep.getDestinationPoint().getName() + " anyway.");
        }).start();


      }
    } else {
      if (!nextStep.isExecutionAllowed()) {
        // 未到达100失败但是之前暂停过，因此通过重新规划恢复任务，根据上次暂停的点和目的地，重新生成TransportOrder
        // 将第一个DriveOrder改为新的，其他的DriveOrder不变
//        reOrder();
        rerouteUtil.reroute(vehicleService.fetchObject(Vehicle.class, vehicle.getReference()));


//              rerouteUtil.reroute(vehicleService.fetchObject(Vehicle.class, vehicle.getReference()));
//              nextStep.setExecutionAllowed(true);
        LOG.warn("Already tried " + tryLockFailCount + " times, recovery for all vehicles because path " + nextStep.getPath().getName() + " is available again.");
        tryLockFailCount = 0;
      }
    }
  }

  synchronized private void reRoute(Step nextStep) {
    //中间不能被打断，否则可能会有别的线程改拓扑，比如那个3s后自动恢复的线程，导致总是找不到路径
    changeTopology(nextStep);
    rerouteUtil.reroute(vehicleService.fetchObject(Vehicle.class, vehicle.getReference()));
  }

  private void changeTopology(Step nextStep) {
    routerService.updatePathLock(nextStep.getPath().getReference(), true);
//    String failedPoint = nextStep.getDestinationPoint().getName();
//    if (paths.size() > 0) {
//      for (Path p : paths) {
//        if (p.getDestinationPoint().getName().equals(failedPoint) || p.getSourcePoint().getName().equals(failedPoint)) {
//          routerService.updatePathLock(p.getReference(), true);
//        }
//      }
//    }
  }

  private void reOrder() {
    LOG.warn("ReOrdering, curPosition is " + commAdapter.getProcessModel().getVehiclePosition());
    List<DestinationCreationTO> destinations = new LinkedList<>();
    destinations.add(new DestinationCreationTO(currentDriveOrder.getRoute().getFinalDestinationPoint().getName(),
            DriveOrder.Destination.OP_MOVE));
    TransportOrderCreationTO orderTO
            = new TransportOrderCreationTO("MyTransportOrder-" + UUID.randomUUID(),
            destinations)
            .withIntendedVehicleName(vehicle.getName());
    TransportOrder dummyOrder = transportOrderService.createTransportOrder(orderTO);
    dispatcherService.dispatch();
    LOG.warn("NewOrder to dispatch is " + dummyOrder.toString());
    LOG.warn("CurOrder to withdraw is " + currentDriveOrder.getTransportOrder().toString());
    dispatcherService.withdrawByTransportOrder(currentDriveOrder.getTransportOrder(), true);
  }

  private void clearLocksExcept(String pointName) {
    Map<String, String> map = objectPool.getSharedLockInformation();
    for (Map.Entry<String, String> entry : map.entrySet()) {
      if (vehicle.getName().equals(entry.getValue()) &&
              !pointName.equals(entry.getKey())) {
        map.remove(entry.getKey());
      }
    }
  }

  private boolean tryLockStep(Step s) {
    String pointToBeLocked = s.getDestinationPoint().getName();
    // 请求锁失败
    if (objectPool.getSharedLockInformation().containsKey(pointToBeLocked)
            && !objectPool.getSharedLockInformation().get(pointToBeLocked).equals(vehicle.getName())) {
      return false;
    } else {
      // 请求锁成功
      objectPool.getSharedLockInformation().put(pointToBeLocked, vehicle.getName());
      LOG.warn("Lock success for point " + s.getDestinationPoint().getName());
      return true;
    }
  }

  @Override
  @SuppressWarnings("deprecation")
  public void terminate() {
    if (!isInitialized()) {
      return;
    }
    // 0912
    if (checkVehicleStateThread != null) {
      checkVehicleStateThread.stop();
    }

    commAdapter.getProcessModel().removePropertyChangeListener(this);
    // Reset the vehicle's position.
    updatePosition(null, null);
    vehicleService.updateVehiclePrecisePosition(vehicle.getReference(), null);
    // Free all allocated resources.
    freeAllResources();

    updateCommAdapterState(VehicleCommAdapter.State.UNKNOWN);
    updateVehicleState(Vehicle.State.UNKNOWN);

    eventBus.unsubscribe(this);

    initialized = false;
  }

  @Override
  public void propertyChange(PropertyChangeEvent evt) {
    if (evt.getSource() != commAdapter.getProcessModel()) {
      return;
    }

    handleProcessModelEvent(evt);
  }

  @Override
  public void onEvent(Object event) {
    if (!(event instanceof TCSObjectEvent)) {
      return;
    }

    TCSObjectEvent objectEvent = (TCSObjectEvent) event;
    if (objectEvent.getType() != TCSObjectEvent.Type.OBJECT_MODIFIED) {
      return;
    }

    if (!(objectEvent.getCurrentOrPreviousObjectState() instanceof Vehicle)) {
      return;
    }

    if (!(Objects.equals(objectEvent.getCurrentOrPreviousObjectState().getName(),
            vehicle.getName()))) {
      return;
    }

    Vehicle prevVehicleState = (Vehicle) objectEvent.getPreviousObjectState();
    Vehicle currVehicleState = (Vehicle) objectEvent.getCurrentObjectState();

    if (prevVehicleState.getIntegrationLevel() != currVehicleState.getIntegrationLevel()) {
      onIntegrationLevelChange(prevVehicleState.getIntegrationLevel(),
              currVehicleState.getIntegrationLevel());
    }
  }

  @Override
  public void setDriveOrder(@Nonnull DriveOrder newOrder,
                            @Nonnull Map<String, String> orderProperties)
          throws IllegalStateException {
    synchronized (commAdapter) {
      requireNonNull(newOrder, "newOrder");
      requireNonNull(orderProperties, "orderProperties");
      requireNonNull(newOrder.getRoute(), "newOrder.getRoute()");
      // Assert that there isn't still is a drive order that hasn't been finished/removed, yet.
      checkState(currentDriveOrder == null,
              "%s still has an order! Current order: %s, new order: %s",
              vehicle.getName(),
              currentDriveOrder,
              newOrder);

      scheduler.claim(this, asResourceSequence(newOrder.getRoute().getSteps()));

      currentDriveOrder = newOrder;

      lastCommandExecuted = null;
      vehicleService.updateVehicleRouteProgressIndex(vehicle.getReference(),
              Vehicle.ROUTE_INDEX_DEFAULT);
      createFutureCommands(newOrder, orderProperties);

      // Modify start
      ArrayList<MovementCommand> fCommands = new ArrayList<>(futureCommands);
      String sourcePoint = fCommands.get(0).getStep().getSourcePoint().getName();
      // 恢复拓扑图
      recoveryTopology(sourcePoint);
      // Clear locks in the vehicle's last driveOrder except the startPoint(the last driveOrder's endPoint).
      clearLocksExcept(sourcePoint);
      LOG.warn("ClearLocks when start.");
      setCleared(false);
      if (fCommands.size() > 1) {
        // Try to lock curStep and nextStep when begin a driveOrder.
        if (!tryLockStep(fCommands.get(0).getStep())) {
          fCommands.get(0).getStep().setExecutionAllowed(false);
        } else if (!tryLockStep(fCommands.get(1).getStep())) {
          fCommands.get(1).getStep().setExecutionAllowed(false);
        } else {
          LOG.warn("lock 1,2st point success.");
        }
      } else if (fCommands.size() == 1) {
        if (!tryLockStep(fCommands.get(0).getStep())) {
          fCommands.get(0).getStep().setExecutionAllowed(false);
        }
      }
      // Modify end


      if (canSendNextCommand()) {
        allocateForNextCommand();
      }

      // Set the vehicle's next expected position.
      Point nextPoint = newOrder.getRoute().getSteps().get(0).getDestinationPoint();
      vehicleService.updateVehicleNextPosition(vehicle.getReference(),
              nextPoint.getReference());
    }
  }

  private void recoveryTopology(String sourcePoint) {
    Map<String, List<TCSObjectReference<Path>>> map = objectPool.getSharedTopologyInformation();
    List<TCSObjectReference<Path>> list = map.get(sourcePoint);
    if (list != null) {
      for (TCSObjectReference<Path> p : list) {
        routerService.updatePathLock(p, false);
      }
      map.remove(sourcePoint);
    }
  }

  @Override
  public void updateDriveOrder(@Nonnull DriveOrder newOrder,
                               @Nonnull Map<String, String> orderProperties)
          throws IllegalStateException {
    synchronized (commAdapter) {
      checkState(currentDriveOrder != null, "There's no drive order to be updated");
      requireNonNull(newOrder, "newOrder");

      checkArgument(driveOrdersContinual(currentDriveOrder, newOrder),
              "The new drive order contains steps the vehicle didn't process for the current "
                      + "drive order.");

      // XXX Be a bit more thoughtful of which resource to claim/unclaim
      // XXX Unclaim only resources that would have been allocated in the future...
      scheduler.unclaim(this);
      // XXX ...and therefore claim only the resource that now will be allocated in the future
      scheduler.claim(this, asResourceSequence(newOrder.getRoute().getSteps()));

      // Update the current drive order and future commands
      currentDriveOrder = newOrder;
      // There is a new drive order, so discard all the future/scheduled commands of the old one.
      discardFutureCommands();

      createFutureCommands(newOrder, orderProperties);
      // The current drive order got updated but our queue of future commands now contains commands
      // that have already been processed, so discard these
      discardSentFutureCommands();

      // Get an up-tp-date copy of the vehicle
      Vehicle updatedVehicle = vehicleService.fetchObject(Vehicle.class, vehicle.getReference());
      // Trigger the vehicle's route to be re-drawn
      vehicleService.updateVehicleRouteProgressIndex(vehicle.getReference(),
              updatedVehicle.getRouteProgressIndex());


      // Modify start
      ArrayList<MovementCommand> fCommands = new ArrayList<>(futureCommands);
      String sourcePoint = fCommands.get(0).getStep().getSourcePoint().getName();
      // 恢复拓扑图
      recoveryTopology(sourcePoint);
      // Clear locks in the vehicle's last driveOrder except the startPoint(the last driveOrder's endPoint).
      clearLocksExcept(sourcePoint);
      LOG.warn("ClearLocks when restart after reroute.");
      setCleared(false);
      if (fCommands.size() > 1) {
        // Try to lock curStep and nextStep when begin a driveOrder.
        if (!tryLockStep(fCommands.get(0).getStep())) {
          fCommands.get(0).getStep().setExecutionAllowed(false);
        } else if (!tryLockStep(fCommands.get(1).getStep())) {
          fCommands.get(1).getStep().setExecutionAllowed(false);
        } else {
          LOG.warn("lock 1,2st point success.");
        }
      } else if (fCommands.size() == 1) {
        if (!tryLockStep(fCommands.get(0).getStep())) {
          fCommands.get(0).getStep().setExecutionAllowed(false);
        }
      }
      // Modify end


      // The vehilce may now process previously restricted steps
      if (updatedVehicle.getState() == Vehicle.State.IDLE
              && canSendNextCommand()) {
        allocateForNextCommand();
      }
    }
  }

  private boolean driveOrdersContinual(DriveOrder oldOrder, DriveOrder newOrder) {
    LOG.debug("Checking drive order continuity for {} and {}.", oldOrder, newOrder);

    // Get an up-tp-date copy of the vehicle
    Vehicle updatedVehicle = vehicleService.fetchObject(Vehicle.class, vehicle.getReference());
    int routeProgessIndex = updatedVehicle.getRouteProgressIndex();
    if (routeProgessIndex == -1) {
      return true;
    }

    List<Step> oldSteps = oldOrder.getRoute().getSteps();
    List<Step> newSteps = newOrder.getRoute().getSteps();

    List<Step> oldProcessedSteps = oldSteps.subList(0, routeProgessIndex + 1);
    List<Step> newProcessedSteps = newSteps.subList(0, routeProgessIndex + 1);

    LOG.debug("Comparing {} and {} for equality.", oldProcessedSteps, newProcessedSteps);
    return Objects.equals(oldProcessedSteps, newProcessedSteps);
  }

  private void discardFutureCommands() {
    futureCommands.clear();
    if (waitingForAllocation) {
      LOG.debug("{}: Discarding pending command but still waiting for allocation: {}",
              vehicle.getName(),
              pendingCommand);
    }
    pendingCommand = null;
  }

  private void discardSentFutureCommands() {
    MovementCommand lastCommandSent;
    if (commandsSent.isEmpty()) {
      if (lastCommandExecuted == null) {
        // There are no commands to be dicarded
        return;
      } else {
        // No commands in the 'sent queue', but the vehicle already executed some commands 
        lastCommandSent = lastCommandExecuted;
      }
    } else {
      List<MovementCommand> commandsSentList = new ArrayList<>(commandsSent);
      lastCommandSent = commandsSentList.get(commandsSentList.size() - 1);
    }

    LOG.debug("Discarding future commands up to '{}' (inclusively): {}",
            lastCommandSent,
            futureCommands);
    for (int i = 0; i < lastCommandSent.getStep().getRouteIndex() + 1; i++) {
      futureCommands.poll();
    }
  }

  @Override
  public void clearDriveOrder() {
    synchronized (commAdapter) {
      currentDriveOrder = null;

      // Clear pending resource allocations. If they still arrive, we will
      // refuse them in allocationSuccessful().
      waitingForAllocation = false;
      pendingResources = null;

      vehicleService.updateVehicleRouteProgressIndex(vehicle.getReference(),
              Vehicle.ROUTE_INDEX_DEFAULT);
    }
  }

  @Override
  public void abortDriveOrder() {
    synchronized (commAdapter) {
      if (currentDriveOrder == null) {
        LOG.debug("{}: No drive order to be aborted", vehicle.getName());
        return;
      }
      futureCommands.clear();
    }
  }

  @Override
  public void clearCommandQueue() {
    synchronized (commAdapter) {
      commAdapter.clearCommandQueue();
      commandsSent.clear();
      futureCommands.clear();
      pendingCommand = null;
      // Free all resource sets that were reserved for future commands, except the current one...
      Set<TCSResource<?>> neededResources = allocatedResources.poll();
      for (Set<TCSResource<?>> resSet : allocatedResources) {
        if (resSet != null) {
          scheduler.free(this, resSet);
        }
      }
      allocatedResources.clear();
      // Put the resources for the current command/position back in...
      allocatedResources.add(neededResources);
    }
  }

  @Override
  @Deprecated
  public void resetVehiclePosition() {
    synchronized (commAdapter) {
      checkState(currentDriveOrder == null, "%s: Vehicle has a drive order", vehicle.getName());
      checkState(!waitingForAllocation,
              "%s: Vehicle is waiting for resource allocation",
              vehicle.getName());

      setVehiclePosition(null);
    }
  }

  @Override
  @Nonnull
  public ExplainedBoolean canProcess(@Nonnull List<String> operations) {
    requireNonNull(operations, "operations");

    synchronized (commAdapter) {
      return commAdapter.canProcess(operations);
    }
  }

  @Override
  public void sendCommAdapterMessage(@Nullable Object message) {
    synchronized (commAdapter) {
      commAdapter.processMessage(message);
    }
  }

  @Override
  public void sendCommAdapterCommand(AdapterCommand command) {
    synchronized (commAdapter) {
      commAdapter.execute(command);
    }
  }

  @Override
  public Queue<MovementCommand> getCommandsSent() {
    return new LinkedList<>(commandsSent);
  }

  @Override
  @Nonnull
  public String getId() {
    return vehicle.getName();
  }

  @Override
  public boolean allocationSuccessful(@Nonnull Set<TCSResource<?>> resources) {
    requireNonNull(resources, "resources");

    // Look up the command the resources were required for.
    MovementCommand command;
    synchronized (commAdapter) {
      // Check if we've actually been waiting for these resources now. If not,
      // let the scheduler know that we don't want them.
      if (!Objects.equals(resources, pendingResources)) {
        LOG.warn("{}: Allocated resources ({}) != pending resources ({}), refusing them",
                vehicle.getName(),
                resources,
                pendingResources);
        return false;
      }

      command = pendingCommand;
      // If there was no command in the queue, it must have been withdrawn in
      // the meantime - let the scheduler know that we don't need the resources
      // any more.
      if (command == null) {
        LOG.warn("{}: No pending command, pending resources = {}, refusing allocated resources: {}",
                vehicle.getName(),
                pendingResources,
                resources);
        waitingForAllocation = false;
        pendingResources = null;
        // In case the contoller's vehicle got rerouted while waiting for resource allocation
        // the pending command is reset and therefore the associated allocation will be ignored. 
        // Since there's now a new/updated route we need to trigger the next allocation. Otherwise
        // the vehicle would wait forever to get the next command.
        if (canSendNextCommand()) {
          allocateForNextCommand();
        }
        return false;
      }
      pendingCommand = null;
      pendingResources = null;

      allocatedResources.add(resources);
      // Send the command to the communication adapter.
      checkState(commAdapter.enqueueCommand(command),
              "Comm adapter did not accept command");
      commandsSent.add(command);

      // Check if the communication adapter has capacity for another command.
      waitingForAllocation = false;
      if (canSendNextCommand()) {
        allocateForNextCommand();
      }
    }
    // Let the scheduler know we've accepted the resources given.
    return true;
  }

  @Override
  public void allocationFailed(@Nonnull Set<TCSResource<?>> resources) {
    requireNonNull(resources, "resources");
    throw new IllegalStateException("Failed to allocate: " + resources);
  }

  @Override
  public String toString() {
    return "DefaultVehicleController{" + "vehicleName=" + vehicle.getName() + '}';
  }

  @SuppressWarnings({"unchecked", "deprecation"})
  private void handleProcessModelEvent(PropertyChangeEvent evt) {
    eventBus.onEvent(new ProcessModelEvent(evt.getPropertyName(),
            commAdapter.createTransferableProcessModel()));

    if (Objects.equals(evt.getPropertyName(), VehicleProcessModel.Attribute.POSITION.name())) {
      updateVehiclePosition((String) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.PRECISE_POSITION.name())) {
      updateVehiclePrecisePosition((Triple) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.ORIENTATION_ANGLE.name())) {
      vehicleService.updateVehicleOrientationAngle(vehicle.getReference(),
              (Double) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.ENERGY_LEVEL.name())) {
      vehicleService.updateVehicleEnergyLevel(vehicle.getReference(), (Integer) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.LOAD_HANDLING_DEVICES.name())) {
      vehicleService.updateVehicleLoadHandlingDevices(vehicle.getReference(),
              (List<LoadHandlingDevice>) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(), VehicleProcessModel.Attribute.STATE.name())) {
      updateVehicleState((Vehicle.State) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.COMM_ADAPTER_STATE.name())) {
      updateCommAdapterState((VehicleCommAdapter.State) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.COMMAND_EXECUTED.name())) {
      commandExecuted((MovementCommand) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.COMMAND_FAILED.name())) {
      dispatcherService.withdrawByVehicle(vehicle.getReference(), true, false);
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.USER_NOTIFICATION.name())) {
      notificationService.publishUserNotification((UserNotification) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.COMM_ADAPTER_EVENT.name())) {
      eventBus.onEvent((VehicleCommAdapterEvent) evt.getNewValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.VEHICLE_PROPERTY.name())) {
      VehicleProcessModel.VehiclePropertyUpdate propUpdate
              = (VehicleProcessModel.VehiclePropertyUpdate) evt.getNewValue();
      vehicleService.updateObjectProperty(vehicle.getReference(),
              propUpdate.getKey(),
              propUpdate.getValue());
    } else if (Objects.equals(evt.getPropertyName(),
            VehicleProcessModel.Attribute.TRANSPORT_ORDER_PROPERTY.name())) {
      VehicleProcessModel.TransportOrderPropertyUpdate propUpdate
              = (VehicleProcessModel.TransportOrderPropertyUpdate) evt.getNewValue();
      if (currentDriveOrder != null) {
        vehicleService.updateObjectProperty(currentDriveOrder.getTransportOrder(),
                propUpdate.getKey(),
                propUpdate.getValue());
      }
    }
  }

  private void updateVehiclePrecisePosition(Triple precisePosition)
          throws ObjectUnknownException {
    // Get an up-to-date copy of the vehicle
    Vehicle currVehicle = vehicleService.fetchObject(Vehicle.class, vehicle.getReference());

    if (currVehicle.getIntegrationLevel() != Vehicle.IntegrationLevel.TO_BE_IGNORED) {
      vehicleService.updateVehiclePrecisePosition(vehicle.getReference(), precisePosition);
    }
  }

  private void updateVehiclePosition(String position) {


    // update sharedMap
    Map<String, String> sharedMap = objectPool.getSharedMap();
    sharedMap.put(vehicle.getName(), position);


    // Get an up-to-date copy of the vehicle
    Vehicle currVehicle = vehicleService.fetchObject(Vehicle.class, vehicle.getReference());

    if (currVehicle.getIntegrationLevel() == Vehicle.IntegrationLevel.TO_BE_RESPECTED
            || currVehicle.getIntegrationLevel() == Vehicle.IntegrationLevel.TO_BE_UTILIZED) {
      setVehiclePosition(position);
    } else if (currVehicle.getIntegrationLevel() == Vehicle.IntegrationLevel.TO_BE_NOTICED) {
      Point point = vehicleService.fetchObject(Point.class, position);
      updatePosition(toReference(point), null);
    }
  }

  private void setVehiclePosition(String position) {
    // Place the vehicle on the given position, regardless of what the kernel
    // might expect. The vehicle is physically there, even if it shouldn't be.
    // The same is true for null values - if the vehicle says it's not on any
    // known position, it has to be treated as a fact.
    Point point;
    if (position == null) {
      point = null;
    } else {
      point = vehicleService.fetchObject(Point.class, position);
      // If the new position is not in the model, ignore it. (Some vehicles/drivers send 
      // intermediate positions that cannot be order destinations and thus do not exist in
      // the model.
      if (point == null) {
        LOG.warn("{}: At unknown position {}", vehicle.getName(), position);
        return;
      }
    }
    synchronized (commAdapter) {
      // If the current drive order is null, just set the vehicle's position.
      if (currentDriveOrder == null) {
        LOG.debug("{}: Reported new position {} and we do not have a drive order.",
                vehicle.getName(),
                point);
        updatePositionWithoutOrder(point);
      } else if (commandsSent.isEmpty()) {
        // We have a drive order, but can't remember sending a command to the
        // vehicle. Just set the position without touching the resources, as
        // that might cause even more damage when we actually send commands
        // to the vehicle.
        LOG.debug("{}: Reported new position {} and we didn't send any commands of drive order.",
                vehicle.getName(),
                point);
        updatePosition(toReference(point), null);
      } else {
        updatePositionWithOrder(position, point);
      }
    }
  }

  private void commandExecuted(MovementCommand executedCommand) {
    requireNonNull(executedCommand, "executedCommand");

    synchronized (commAdapter) {
      // Check if the executed command is the one we expect at this point.
      MovementCommand expectedCommand = commandsSent.peek();
      if (!Objects.equals(expectedCommand, executedCommand)) {
        LOG.warn("{}: Communication adapter executed unexpected command: {} != {}",
                vehicle.getName(),
                executedCommand,
                expectedCommand);
        // XXX The communication adapter executed an unexpected command. Do something!
      }
      // Remove the command from the queue, since it has been processed successfully.
      lastCommandExecuted = commandsSent.remove();
      // Free resources allocated for the command before the one now executed.
      Set<TCSResource<?>> oldResources = allocatedResources.poll();
      if (oldResources != null) {
        LOG.debug("{}: Freeing resources: {}", vehicle.getName(), oldResources);
        scheduler.free(this, oldResources);
      } else {
        LOG.debug("{}: Nothing to free.", vehicle.getName());
      }
      // Check if there are more commands to be processed for the current drive order.
      if (pendingCommand == null && futureCommands.isEmpty()) {
        LOG.debug("{}: No more commands in current drive order", vehicle.getName());
        // Check if there are still commands that have been sent to the communication adapter but
        // not yet executed. If not, the whole order has been executed completely - let the kernel
        // know about that so it can give us the next drive order.
        if (commandsSent.isEmpty() && !waitingForAllocation) {
          LOG.debug("{}: Current drive order processed", vehicle.getName());
          currentDriveOrder = null;
          // Let the kernel/dispatcher know that the drive order has been processed completely (by
          // setting its state to AWAITING_ORDER).
          vehicleService.updateVehicleRouteProgressIndex(vehicle.getReference(),
                  Vehicle.ROUTE_INDEX_DEFAULT);
          vehicleService.updateVehicleProcState(vehicle.getReference(),
                  Vehicle.ProcState.AWAITING_ORDER);
        }
      }
      // There are more commands to be processed.
      // Check if we can send another command to the comm adapter.
      else if (canSendNextCommand()) {
        allocateForNextCommand();
      }
    }
  }

  private void createFutureCommands(DriveOrder newOrder, Map<String, String> orderProperties) {
    // Start processing the new order, i.e. fill futureCommands with corresponding command objects.
    String op = newOrder.getDestination().getOperation();
    Route orderRoute = newOrder.getRoute();
    Point finalDestination = orderRoute.getFinalDestinationPoint();
    Location finalDestinationLocation
            = vehicleService.fetchObject(Location.class,
            newOrder.getDestination().getDestination().getName());
    Map<String, String> destProperties = newOrder.getDestination().getProperties();
    Iterator<Step> stepIter = orderRoute.getSteps().iterator();
    while (stepIter.hasNext()) {
      Step curStep = stepIter.next();
      // Ignore report positions on the route.
      if (curStep.getDestinationPoint().isHaltingPosition()) {
        boolean isFinalMovement = !stepIter.hasNext();

        String operation = isFinalMovement ? op : MovementCommand.NO_OPERATION;
        Location location = isFinalMovement ? finalDestinationLocation : null;

        futureCommands.add(new MovementCommand(curStep,
                operation,
                location,
                isFinalMovement,
                finalDestinationLocation,
                finalDestination,
                op,
                mergeProperties(orderProperties, destProperties)));
      }
    }
  }

  @SuppressWarnings("deprecation")
  private void updateCommAdapterState(VehicleCommAdapter.State newState) {
    commAdapterState = requireNonNull(newState, "newState");
    localKernel.setVehicleAdapterState(vehicle.getReference(), newState);
  }

  @SuppressWarnings("deprecation")
  private void updateVehicleState(Vehicle.State newState) {
    requireNonNull(newState, "newState");
    // If the communication adapter knows the state of the vehicle and is not
    // marked as connected with us, mark it as connected now. - It knows the
    // vehicle's state, so it must be connected to it.
    if (!Vehicle.State.UNKNOWN.equals(newState)
            && !VehicleCommAdapter.State.CONNECTED.equals(commAdapterState)) {
      updateCommAdapterState(VehicleCommAdapter.State.CONNECTED);
    }
    vehicleService.updateVehicleState(vehicle.getReference(), newState);
  }

  /**
   * Checks if we can send another command to the communication adapter without
   * overflowing its capacity and with respect to the number of commands still
   * in our queue and allocation requests to the scheduler in progress.
   *
   * @return <code>true</code> if, and only if, we can send another command.
   */
  private boolean canSendNextCommand() {
    int sendableCommands = Math.min(commAdapter.getCommandQueueCapacity() - commandsSent.size(),
            futureCommands.size());
    if (sendableCommands <= 0) {
      LOG.debug("{}: Cannot send, number of sendable commands: {}",
              vehicle.getName(),
              sendableCommands);
      return false;
    }
    if (!futureCommands.peek().getStep().isExecutionAllowed()) {
      LOG.debug("{}: Cannot send, movement execution is not allowed", vehicle.getName());
      return false;
    }
    if (waitingForAllocation) {
      LOG.debug("{}: Cannot send, waiting for allocation", vehicle.getName());
      return false;
    }
    return true;
  }

  /**
   * Allocate the resources needed for executing the next command.
   */
  private void allocateForNextCommand() {
    checkState(pendingCommand == null, "pendingCommand != null");

    // Find out which resources are actually needed for the next command.
    MovementCommand moveCmd = futureCommands.poll();
    pendingResources = getNeededResources(moveCmd);
    LOG.debug("{}: Allocating resources: {}", vehicle.getName(), pendingResources);
    scheduler.allocate(this, pendingResources);
    // Remember that we're waiting for an allocation. This ensures that we only
    // wait for one allocation at a time, and that we get the resources from the
    // scheduler in the right order.
    waitingForAllocation = true;
    pendingCommand = moveCmd;
  }

  /**
   * Returns a set of resources needed for executing the given command.
   *
   * @param cmd The command for which to return the needed resources.
   * @return A set of resources needed for executing the given command.
   */
  private Set<TCSResource<?>> getNeededResources(MovementCommand cmd) {
    requireNonNull(cmd, "cmd");

    Set<TCSResource<?>> result = new HashSet<>();
    result.add(cmd.getStep().getDestinationPoint());
    if (cmd.getStep().getPath() != null) {
      result.add(cmd.getStep().getPath());
    }
    return result;
  }

  /**
   * Frees all resources allocated for the vehicle.
   */
  private void freeAllResources() {
    scheduler.freeAll(this);
    allocatedResources.clear();
  }

  /**
   * Returns the next command expected to be executed by the vehicle, skipping the current one.
   *
   * @return The next command expected to be executed by the vehicle.
   */
  private MovementCommand findNextCommand() {
    MovementCommand nextCommand = commandsSent.stream()
            .skip(1)
            .filter(cmd -> cmd != null)
            .findFirst()
            .orElse(null);

    if (nextCommand == null) {
      nextCommand = pendingCommand;
    }

    if (nextCommand == null) {
      futureCommands.stream()
              .filter(cmd -> cmd != null)
              .findFirst()
              .orElse(null);
    }

    return nextCommand;
  }

  private void updatePositionWithoutOrder(Point point) {
    // Allocate only the resources required for occupying the new position.
    freeAllResources();
    // If the vehicle is at an unknown position, it's impossible to say
    // which resources it needs, so don't allocate any in that case.
    if (point != null) {
      try {
        Set<TCSResource<?>> requiredResource = new HashSet<>();
        requiredResource.add(point);
        scheduler.allocateNow(this, requiredResource);
        allocatedResources.add(requiredResource);
      } catch (ResourceAllocationException exc) {
        LOG.warn("{}: Could not allocate required resources immediately, ignored.",
                vehicle.getName(),
                exc);
      }
    }
    updatePosition(toReference(point), null);
  }

  private void updatePositionWithOrder(String position, Point point) {
    // If a drive order is being processed, check if the reported position
    // is the one we expect.
    MovementCommand moveCommand = commandsSent.stream().findFirst().get();

    Point dstPoint = moveCommand.getStep().getDestinationPoint();
    if (dstPoint.getName().equals(position)) {
      // Update the vehicle's progress index.
      vehicleService.updateVehicleRouteProgressIndex(vehicle.getReference(),
              moveCommand.getStep().getRouteIndex());
      // Let the scheduler know where we are now.
      scheduler.updateProgressIndex(this, moveCommand.getStep().getRouteIndex());
    } else if (position == null) {
      LOG.info("{}: Resetting position for vehicle", vehicle.getName());
    } else {
      LOG.warn("{}: Reported position: {}, expected: {}",
              vehicle.getName(),
              position,
              dstPoint.getName());
    }

    updatePosition(toReference(point), extractNextPosition(findNextCommand()));
  }

  private void updatePosition(TCSObjectReference<Point> posRef,
                              TCSObjectReference<Point> nextPosRef) {
    vehicleService.updateVehiclePosition(vehicle.getReference(), posRef);
    vehicleService.updateVehicleNextPosition(vehicle.getReference(), nextPosRef);
  }

  private void onIntegrationLevelChange(Vehicle.IntegrationLevel prevIntegrationLevel,
                                        Vehicle.IntegrationLevel currIntegrationLevel) {
    synchronized (commAdapter) {
      if (currIntegrationLevel == Vehicle.IntegrationLevel.TO_BE_IGNORED) {
        // Reset the vehicle's position to free all allocated resources
        resetVehiclePosition();
        vehicleService.updateVehiclePrecisePosition(vehicle.getReference(), null);
      } else if (currIntegrationLevel == Vehicle.IntegrationLevel.TO_BE_NOTICED) {
        // Reset the vehicle's position to free all allocated resources
        resetVehiclePosition();

        // Update the vehicle's position in its model, but don't allocate any resources
        VehicleProcessModel processModel = commAdapter.getProcessModel();
        if (processModel.getVehiclePosition() != null) {
          Point point = vehicleService.fetchObject(Point.class, processModel.getVehiclePosition());
          vehicleService.updateVehiclePosition(vehicle.getReference(), point.getReference());
        }
        vehicleService.updateVehiclePrecisePosition(vehicle.getReference(),
                processModel.getVehiclePrecisePosition());
      } else if ((currIntegrationLevel == Vehicle.IntegrationLevel.TO_BE_RESPECTED
              || currIntegrationLevel == Vehicle.IntegrationLevel.TO_BE_UTILIZED)
              && (prevIntegrationLevel == Vehicle.IntegrationLevel.TO_BE_IGNORED
              || prevIntegrationLevel == Vehicle.IntegrationLevel.TO_BE_NOTICED)) {
        // Allocate the vehicle's current position and implicitly update its model's position
        allocateVehiclePosition();
      }

      // XXX In the future the integration level won't implicitly affect the proc state, anymore
      if (currIntegrationLevel == Vehicle.IntegrationLevel.TO_BE_UTILIZED) {
        if (vehicle.hasProcState(Vehicle.ProcState.UNAVAILABLE)) {
          vehicleService.updateVehicleProcState(vehicle.getReference(), Vehicle.ProcState.IDLE);
        }
      }
    }
  }

  private void allocateVehiclePosition() {
    VehicleProcessModel processModel = commAdapter.getProcessModel();
    // We don't want to set the vehicle position right away, since the vehicle's currently
    // allocated resources would be freed in the first place. We need to check, if the vehicle's 
    // current position is already part of it's allocated resoruces.
    if (!alreadyAllocated(processModel.getVehiclePosition())) {
      // Set vehicle's position to allocate the resources
      setVehiclePosition(processModel.getVehiclePosition());
      vehicleService.updateVehiclePrecisePosition(vehicle.getReference(),
              processModel.getVehiclePrecisePosition());
    }
  }

  private boolean alreadyAllocated(String position) {
    return allocatedResources.stream()
            .filter(resources -> resources != null)
            .flatMap(resources -> resources.stream())
            .anyMatch(resource -> resource.getName().equals(position));
  }

  private static TCSObjectReference<Point> toReference(Point point) {
    return point == null ? null : point.getReference();
  }

  private static TCSObjectReference<Point> extractNextPosition(MovementCommand nextCommand) {
    if (nextCommand == null) {
      return null;
    } else {
      return nextCommand.getStep().getDestinationPoint().getReference();
    }
  }

  /**
   * Merges the properties of a transport order and those of a drive order.
   *
   * @param orderProps The properties of a transport order.
   * @param destProps  The properties of a drive order destination.
   * @return The merged properties.
   */
  private static Map<String, String> mergeProperties(Map<String, String> orderProps,
                                                     Map<String, String> destProps) {
    requireNonNull(orderProps, "orderProps");
    requireNonNull(destProps, "destProps");

    Map<String, String> result = new HashMap<>();
    result.putAll(orderProps);
    result.putAll(destProps);
    return result;
  }

  private static List<Set<TCSResource<?>>> asResourceSequence(@Nonnull List<Route.Step> steps) {
    requireNonNull(steps, "steps");

    List<Set<TCSResource<?>>> result = new ArrayList<>(steps.size());
    for (Route.Step step : steps) {
      result.add(new HashSet<>(Arrays.asList(step.getDestinationPoint(), step.getPath())));
    }
    return result;
  }
}
