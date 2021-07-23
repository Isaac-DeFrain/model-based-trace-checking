extern crate log;
extern crate log4rs;
extern crate chrono;
extern crate rand;

use log::{info, SetLoggerError};
use log4rs::{
    append::file::FileAppender,
    config::{Appender, Config, Root},
    encode::pattern::PatternEncoder,
};
use chrono::Local;
use std::fmt::Display;
use rand::prelude::*;

fn main() -> Result<(), SetLoggerError> {
    const DATE_FMT: &str = "%Y-%m-%d_%H:%M:%S";  
    let level = log::LevelFilter::Info;
    let date = Local::now().format(DATE_FMT).to_string();
    let file_path = format!("./log/{}.txt", &date);

    // Logging to log file.
    let logfile = FileAppender::builder()
        // Pattern: https://docs.rs/log4rs/*/log4rs/encode/pattern/index.html
        .encoder(Box::new(PatternEncoder::new("{m}\n")))
        .build(&file_path)
        .unwrap();

    // Log Info level output to file where trace is the default level
    let config = Config::builder()
        .appender(Appender::builder().build("logfile", Box::new(logfile)))
        .build(
            Root::builder()
                .appender("logfile")
                .build(level),
        )
        .unwrap();

    // Use this to change log levels at runtime.
    // This means you can change the default log level to trace
    // if you are trying to debug an issue and need more logs on then turn it off
    // once you are done.
    let _handle = log4rs::init_config(config)?;

    // Simulation of a counter taking an arbitrary number of steps
    let n: u8 = thread_rng().gen();
    counter_with_logging(n);

    Ok(())
}

// state logging event
pub fn log_event<T: Display>(x: &T) -> () {
  info!("{}", x)
}

// simple counter implementation
pub fn counter_with_logging(n: u8) -> () {
  let x = 0;
  fn incr(n: u8, mut x: i32) -> () {
    if n > 0 {
      let b: bool = thread_rng().gen();
      log_event(&x);
      if b {
        x += 1;
        incr(n - 1, x)
      } else {
        incr(n, x);
      }
    } else {
      log_event(&x)
    }
  }
  incr(n, x)
}
