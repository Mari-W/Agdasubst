# Supplement for `Rewriting the Sigma Calculus`

## Requirements

Agda: [v2.8.0](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html)
Agda `stdlib`: [v2.3](https://agda.readthedocs.io/en/v2.8.0/tools/package-system.html#example-using-the-standard-library) 

Python: [v3.12.12](https://www.python.org/downloads/release/python-31212/)

## Structure

```
├── agda
│   ├── examples.agda  -- contains the code from section 2 and 4
│   └── systemf.agda   -- contains the code from section 3
├── generated
│   ├── signatures
│   │   └── *.sig      -- example signatures from autosubst repo 
│   ├── agda
│   │   └── *.agda     -- files generated from signatures
│   └── agdasubst.py   -- standalone code generation script
└── README.md          -- this file
```