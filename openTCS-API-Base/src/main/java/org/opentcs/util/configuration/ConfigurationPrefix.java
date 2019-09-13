/**
 * Copyright (c) The openTCS Authors.
 *
 * This program is free software and subject to the MIT license. (For details,
 * see the licensing information (LICENSE.txt) you should have received with
 * this copy of the software.)
 */
package org.opentcs.util.configuration;

import java.lang.annotation.Documented;
import static java.lang.annotation.ElementType.TYPE;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;
import org.opentcs.util.annotations.ScheduledApiChange;

/**
 * Marks an interface that provides some configuration for a specific class.
 * 
 * @author Martin Grzenia (Fraunhofer IML)
 * @deprecated Use {@link org.opentcs.configuration.ConfigurationPrefix} instead.
 */
@Target({TYPE})
@Retention(RetentionPolicy.RUNTIME)
@Documented
@Deprecated
@ScheduledApiChange(when = "5.0", details = "Will be removed.")
public @interface ConfigurationPrefix {
  
  /**
   * Returns the name of the class the interface configures.
   * 
   * @return The name of the class the interface configures.
   */
  String value();
}
