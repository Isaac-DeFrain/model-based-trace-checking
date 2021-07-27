# tla

This is where the TLA+ specification and all Java overrides are defined.

## TLA+ modules

The main specification, `ComposedSpec`, is defined in `trace.tla`. This combines the `counter` spec with the trace reader spec.

`Parser.tla` is only used to override the definition of `parse` (defined in `Parser.java`).

`trace_def.tla` is only used to parse the supplied log file and export the resulting `Trace` used in `trace.tla`.

## Java overrides

We use a Java override to define our log file parser in `Parser.java`. There is a corresponding TLA+ module with the same name (i.e. `Parser.tla`) with a declaration of a `parse` operator to effect the override.

The `Parser` module is imported into `trace_def.tla` in order to use the `parse` function to convert the supplied log file into a TLA+ sequence.
