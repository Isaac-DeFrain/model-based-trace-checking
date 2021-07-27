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
pub fn log_state<T, U>(st: &State<T, U>) -> ()
where T: Display, U: Display
{
  // info!("{}", st.json_of_state().as_str())
  info!("{}", st.str_of_state().as_str())
}

// simple counter implementation
pub fn counter_with_logging(n: u8) -> () {
  let mut st = State { x: 0, y: Y::ModelValue(String::from("a")) };
  fn step(n: u8, st: &mut State<i32, bool>) -> () {
    if n > 0 {
      let b: bool = thread_rng().gen();
      log_state(&st);
      if b {
        st.step();
        step(n - 1, st)
      } else {
        step(n, st);
      }
    } else {
      log_state(&st)
    }
  }
  step(n, &mut st)
}

#[derive(PartialEq, Eq, Debug)]
pub enum Y<T: Display> {
  ModelValue(String),
  Value(T)
}

#[derive(PartialEq, Eq, Debug)]
pub struct State<T, U>
where T: Display, U: Display
{
  x: T,
  y: Y<U>
}

#[allow(dead_code)]
impl<T, U> State<T, U>
where T: Display, U: Display
{
  fn json_of_state(&self) -> String {
    let mut acc = String::from("{ ");
    acc.push_str(format!("\"x\" : {} }}", self.x).as_str());
    acc
  }

  fn str_of_state(&self) -> String {
    let mut acc = String::new();
    acc.push_str(format!("{}", self.x).as_str());
    acc.push_str(", ");
    match &self.y {
      Y::ModelValue(v) => acc.push_str(v.as_str()),
      Y::Value(v) => acc.push_str(format!("{}", v).as_str()),
    };
    acc
  }
}

impl State<i32, bool> {
  fn step(&mut self) {
    self.y = if self.x > 20 {
      let y = Y::Value(self.x % 2 == 0);
      y
    } else {
      Y::ModelValue(String::from("a"))
    };
    self.x += 1;
  }
}
