# assoc-minikanren
miniKanren with unification `(== u v)` and association `(assoco k v)` constraints.

```
> (run* (a b c)
        (assoco a 'foo)
        (assoco b 'bar)
        (assoco c 'baz))
'(((_0 _1 _2) ((_0 foo) (_1 bar) (_2 baz))))

> (run* (a b c)
        (assoco a 'foo)
        (assoco b 'bar)
        (assoco c 'baz)
        (== a c))
'()

> (run* (q) (fresh (a b c)
              (conde ((assoco a b)
                      (assoco b c))
                     ((assoco a a)
                      (assoco b b)
                      (assoco c c))
                     ((assoco a `(,b ,c))
                      (assoco a `(,a ,a)))
                     ((assoco a b)
                      (assoco b c)
                      (assoco c a)))))
'(((_0) ((_1 _2) (_3 _1)))
  ((_0) ((_1 _1) (_2 _2) (_3 _3)))
  ((_0) ((_1 (_1 _1))))
  ((_0) ((_1 _2) (_2 _3) (_3 _1))))

> (defrel (patho u v)
    (conde ((== u v))
           ((fresh (m)
              (assoco u m)
              (patho m v)))))

> (run 5 (u v) (patho u v))
'(((_0 _0) ())
  ((_0 _1) ((_0 _1)))
  ((_0 _1) ((_0 _2) (_2 _1)))
  ((_0 _1) ((_0 _3) (_2 _1) (_3 _2)))
  ((_0 _1) ((_0 _4) (_2 _1) (_3 _2) (_4 _3))))
```

## TODO
- Remove association pairs unreachable from the query variables during reification.
- Add support for `=/=`, `absento`, `spmbolo`, `numbero`.
- Explore negative constraints like `(not-assoco k v)` and `(not-key k)`
