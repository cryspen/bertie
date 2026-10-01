# F* proofs

`extraction` holds the F* code that hax generates from the Bertie Rust code.
Regenerate it with

```
./hax-driver.py extract-fstar
```

and typecheck it with

```
./hax-driver.py typecheck
```

Proof annotations live in the Rust source as `hax_lib` attributes, so
`extraction` is never edited by hand.
