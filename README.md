# model-based-trace-checking

This is a very simple POC for model-based trace-checking from Rust. We closely follow Ron Pressler's [*Verifying Software Traces Against a Formal Specification with TLA+ and TLC*](https://pron.github.io/files/Trace.pdf).

The Rust program `src/main.rs` simulates a counter with stuttering steps and generates a new log file with each run.

Once log files have been produced, they can be parsed into TLA+ as a sequence of values with the `parse` function. This sequence represents the trace of the execution. This behavior is then checked against the specification by checking that the model *violates* the specified invariant. Oddly enough, if the behavior (supplied by the trace) is *valid*, TLC will report a violation of the `NotTraceFinished` invariant and provide the given behavior as a conterexample. If the behavior is *invalid*, TLC will report a successful model check.

## Running the code

Clone the repo

```bash
$ git clone https://github.com/Isaac-DeFrain/model-based-trace-checking.git
```

From the `src` directory, run the program

```bash
$ cd model-based-trace-checking/src
$ cargo run
```

A new log file will be generated in the `log` directory. Might as well do `cargo run` a few more times to generate multiple log files.

Now we have some traces logged and we need to check if they conform to the `CombinedSpec` spec.

As mentioned above, the desired TLC output is an *error* along with a counterexample (this is just the supplied trace). If the model check is successful, then the behavior *does not* conform to the specification.

Fortunately, this process has been automated! All you need to do is navigate to the `automate` dir and run the python code there:

```bash
$ cd ../automate
$ python orchestrate.py
```

The result for each log file is printed to stdout.
