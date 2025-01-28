phun
====

This is a simple theorem proof assistant, built on an implementation of MLTT.

Its main purpose is for me to learn about implementing type theories, so don't expect it to be too user-friendly.

Running
-------

If you have a file named "foo.ph", you can typecheck/interpret it by running

```
cabal run phun -- foo.ph
```

Example
-------

Let's look at proving that addition is commutative as an example.

```agda
plus : (Nat -> Nat -> Nat)
λx.λy.NatInd(λ_.Nat, y, λ_.λr.Succ(r), x)

cong : ΠA:Type. ΠB:Type. Πf:(A -> B). Πa:A. Πb:A. (Id(a, b) -> Id(f a, f b))
λ_.λ_.λf.λa.λb.λp.J(λx.λy.λq.Id(f x, f y), λv.Refl(f v), p)

trans : ΠA:Type. Πa:A. Πb:A. Πc:A. (Id(a,b) -> Id(b,c) -> Id(a,c))
λ_.λa.λb.λc.λp.J(λx.λy.λq.Π_:Id(y,c).Id(x,c), λv.λq.q, p)

plusZeroRight : Πn:_. Id(plus n Zero, n)
λn.NatInd(λm.Id(plus m Zero, m), Refl(Zero), λ_.λp.cong _ _ (λx.Succ(x)) _ _ p, n)

plusSucc : Πn:_. Πm:_. Id(plus n Succ(m), Succ(plus n m))
λn.λm.NatInd(λx.Id(plus x Succ(m), Succ(plus x m)), Refl(Succ(m)), λx.λp.cong _ _ (λy.Succ(y)) _ _ p, n)

plusComm : Πn:_. Πm:_. Id(plus n m, plus m n)
λn.λm.NatInd(
  λx.Id(plus n x, plus x n),
  plusZeroRight n,
  λx.λp.trans Nat _ _ _ (plusSucc n x) (cong _ _ (λx.Succ(x)) _ _ p),
  m)

-- If there is an expression at the end of the file, it will be evaluated and printed
plus Succ(Succ(Succ(Zero))) Succ(Succ(Zero))
```
There are also ASCII equivalents for each of the non-ASCII characters.

As you can see, there is no recursion, you have to use the eliminators for each type, e.g. `NatInd` for `Nat` and `J` for `Id`.
At this point there are also no custom types, instead you have to make do with the ones that are built in, which as of now are

- `Typeₙ` - An infinite non-cumulative hierarchy of types, with `Type` at the
  bottom. Universe polymorphism is not supported at this point, so you may have to
  implement a function at multiple levels if you need it at more than one.
- `Πx:A.B` - The type of dependent functions from `A` to `B`.
- `A → B` - This is just syntactic sugar for `Π_:A.B`.
- `⊥` (or `Bottom`) - The type with no inhabitants.
- `⊤` (or `Top`) - The type with only one inhabitant, `TT`.
- `Bool` - The type of booleans.
- `Nat` - The type of natural numbers.
- `Id` - The identity type.

Things to improve
-----------------

- Dependent pairs: For most purposes you should be able to encode them via dependent products, but it would be nice to have them available natively.
- Implicit arguments: You can already pass `_` to let the typechecker figure out what an argument should be, but implicit arguments would be a bit nicer to use.
- Better error reporting: Right now the error messages are pretty bad.
- Type inspection: There should be a way to inspect the type of an expression in a given context.
