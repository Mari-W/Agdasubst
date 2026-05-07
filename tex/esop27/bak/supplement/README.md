# Supplement for `Intrinisically Typed Syntax That Works (Functional Pearl)`

## Requirements

Agda: [v2.8.0](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)
Agda `stdlib`: [v2.3](https://agda.readthedocs.io/en/v2.8.0/tools/package-system.html#example-using-the-standard-library) 

# Structure
- `SystemF.agda`: Intrinsically Typed System F, Expression Monad Laws, Progress, Examples
- `SystemFo.agda`: Intrinsically Typed System Fω, Progress
- `SystemFo-examples.agda`: System Fω Examples (expect long type checking times!)

_**Warning**_: The SystemFω files use a weaker version of the sigma calculus, that is easier to implement, but also safe. It uses slightly different laws.