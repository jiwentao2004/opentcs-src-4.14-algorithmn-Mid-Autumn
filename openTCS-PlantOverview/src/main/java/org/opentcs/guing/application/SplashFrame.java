/*
 * openTCS copyright information:
 * Copyright (c) 2013 Fraunhofer IML
 *
 * This program is free software and subject to the MIT license. (For details,
 * see the licensing information (LICENSE.txt) you should have received with
 * this copy of the software.)
 */
package org.opentcs.guing.application;

import java.lang.reflect.InvocationTargetException;
import javax.swing.JFrame;
import javax.swing.SwingUtilities;
import org.opentcs.util.gui.Icons;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A frame for displaying the progress of longer-running processes.
 *
 * @author Heinz Huber (Fraunhofer IML)
 */
public class SplashFrame
    extends JFrame
    implements ProgressIndicator {

  /**
   * This class's logger.
   */
  private static final Logger log
      = LoggerFactory.getLogger(SplashFrame.class);

  /**
   * Creates new form SplashFrame
   */
  public SplashFrame() {
    initComponents();
  }

  @Override
  public void initialize() {
    // Ensure this method is called on the event dispatcher thread.
    if (!SwingUtilities.isEventDispatchThread()) {
      try {
        SwingUtilities.invokeAndWait(new Runnable() {
          @Override
          public void run() {
            initialize();
          }
        });
      }
      catch (InterruptedException | InvocationTargetException exc) {
        log.warn("Unexpected exception", exc);
      }
      return;
    }
    setVisible(true);
    setProgress(0, "");
  }

  @Override
  public void setProgress(final int percent, final String message) {
    // Ensure this method is called on the event dispatcher thread.
    if (!SwingUtilities.isEventDispatchThread()) {
      try {
        SwingUtilities.invokeAndWait(new Runnable() {
          @Override
          public void run() {
            setProgress(percent, message);
          }
        });
      }
      catch (InterruptedException | InvocationTargetException exc) {
        log.warn("Unexpected exception", exc);
      }
      return;
    }
    labelMessage.setText(message);
    progressBar.setValue(percent);
    update(getGraphics());
    toFront();
  }

  @Override
  public void terminate() {
    // Ensure this method is called on the event dispatcher thread.
    if (!SwingUtilities.isEventDispatchThread()) {
      try {
        SwingUtilities.invokeAndWait(new Runnable() {
          @Override
          public void run() {
            terminate();
          }
        });
      }
      catch (InterruptedException | InvocationTargetException exc) {
        log.warn("Unexpected exception", exc);
      }
      return;
    }
    dispose();
  }

  // CHECKSTYLE:OFF
  /**
   * This method is called from within the constructor to initialize the form.
   * WARNING: Do NOT modify this code. The content of this method is always
   * regenerated by the Form Editor.
   */
  @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {
        java.awt.GridBagConstraints gridBagConstraints;

        panel = new javax.swing.JPanel();
        labelImage = new javax.swing.JLabel();
        labelMessage = new javax.swing.JLabel();
        progressBar = new javax.swing.JProgressBar();

        setDefaultCloseOperation(javax.swing.WindowConstants.DISPOSE_ON_CLOSE);
        java.util.ResourceBundle bundle = java.util.ResourceBundle.getBundle("org/opentcs/guing/res/labels"); // NOI18N
        setTitle(bundle.getString("OpenTCSView.name")); // NOI18N
        setBackground(new java.awt.Color(255, 255, 255));
        setIconImages(Icons.getOpenTCSIcons());
        setUndecorated(true);
        getContentPane().setLayout(new java.awt.GridBagLayout());

        panel.setBackground(new java.awt.Color(255, 255, 255));
        panel.setLayout(new java.awt.GridBagLayout());

        labelImage.setIcon(new javax.swing.ImageIcon(getClass().getResource("/org/opentcs/guing/res/symbols/openTCS/splash.320x152.gif"))); // NOI18N
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.anchor = java.awt.GridBagConstraints.FIRST_LINE_START;
        panel.add(labelImage, gridBagConstraints);

        labelMessage.setBackground(new java.awt.Color(255, 255, 255));
        labelMessage.setFont(new java.awt.Font("Arial", 1, 12)); // NOI18N
        labelMessage.setText(bundle.getString("SplashFrame.startOpenTCS")); // NOI18N
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 1;
        gridBagConstraints.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.SOUTH;
        gridBagConstraints.weightx = 0.5;
        gridBagConstraints.weighty = 0.5;
        gridBagConstraints.insets = new java.awt.Insets(0, 4, 0, 4);
        panel.add(labelMessage, gridBagConstraints);

        progressBar.setBackground(new java.awt.Color(255, 255, 255));
        progressBar.setForeground(new java.awt.Color(153, 153, 255));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.gridy = 2;
        gridBagConstraints.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.SOUTH;
        gridBagConstraints.weighty = 0.5;
        panel.add(progressBar, gridBagConstraints);

        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.fill = java.awt.GridBagConstraints.BOTH;
        gridBagConstraints.weightx = 1.0;
        gridBagConstraints.weighty = 1.0;
        getContentPane().add(panel, gridBagConstraints);

        setSize(new java.awt.Dimension(320, 183));
        setLocationRelativeTo(null);
    }// </editor-fold>//GEN-END:initComponents
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JLabel labelImage;
    private javax.swing.JLabel labelMessage;
    private javax.swing.JPanel panel;
    private javax.swing.JProgressBar progressBar;
    // End of variables declaration//GEN-END:variables
  // CHECKSTYLE:ON
}
