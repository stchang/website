    Title: If You Give a Mouse a Macro
    Date: 2018-08-16T15:05:17
    Tags: by Sam Caldwell

In [Racket][2], programmers can create powerful abstractions by bundling
together a family of values, functions, and syntax extensions in the form of a
new language. These languages are typically untyped. [Turnstile][1] is a new
Racket {library,language} for creating typed languages. Turnstile
provides an easy way to integrate type checking with Racket's existing tools for
describing languages. The technique was invented by fellow PRL'ers and described
in the paper [*Type Systems as Macros*][3].

Unfortunately, Turnstile doesn't lend itself to creating `define`-like binding
forms. In this blog post, I'm going to show you how to add `define`-like
bindings to your Turnstile language by leveraging Racket's extensive
meta-programming toolbox.

<!-- more -->

All of the code for this blog post can be found [on GitHub][14]. To run it, you
will need the Turnstile package (and Racket), which can be installed with `raco
pkg install turnstile`.

## Type Rules in Turnstile

Let's take a look at how we can use Turnstile to define typed language forms.

```racket
(define-typed-syntax (λ ([x:id (~datum :) τ_in:type] ...) e) ≫
  [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
  -------------------------------------------------
  [⊢ (#%plain-lambda- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)])
```

Looking at this item by item, we see:

1. `define-typed-syntax` is the primary way to define a language form in terms
   of its syntactic shape, how it is type checked, the target language term it
   expands to, and its type.
2. The next part is a [`syntax-parse`][4] pattern describing the the shape of
   the syntax this rule applies to. In this case, we're defining `λ` as a macro
   that expects a parenthesized sequence of identifier-colon-type triples,
   describing the formal arguments to the procedure, followed by the body. The
   `type` syntax class is provided by Turnstile, and describes the surface
   syntax of types; internal operations over types use the expanded version of
   the type, which is accessed via the `norm` attribute.
3. The chevron `≫` on the first line signifies that there is only one case in
   this type rule. Some rules, which we will see later, use multiple
   cases to check different kinds of uses.
4. The body of the rule is a sequence of premises, that usually check and
   analyze the types of sub-expressions, followed by a dashed line, and
   then the conclusion, describing the output syntax and its type.
5. Here, the single premise describes how to check the body of the function. The
   context, which associates variables with types, goes to the left of the
   turnstile (`⊢`). For each formal `x`, this lets us know what type `x` has
   when we find a reference to it in `e`. In this rule, we are saying "while
   checking the right-hand-side, assume `x`---which will be renamed to
   `x-`---has type `τ_in`, for each triple in the input syntax (signified by the
   ellipses `...`)". More on the "renaming to `x-`" in a bit.
6. To the right of the turnstile, we write the expression we are checking, `e`,
   as well as a binding for the syntax that `e` produces while we expand and
   check it, `e-`, as well as the type `τ_out` inferred for `e`.
7. After the dashes comes the conclusion, which begins with `⊢`. The next part
   specifies the expanded syntax of the term. Here, the meaning of the typed `λ`
   is given in terms of Racket's [`#%plain-lambda`][5] (Turnstile uses the
   convention of a `-` suffix for forms in the untyped/target language). The
   final part describes the type of the expression.
   
### Renaming Typed Variables
   
Turnstile lets the Racket expander take care of the details of variable scope,
shadowing, etc. To associate identifier `x` with type `τ`, Turnstile binds `x`
to a macro that knows `τ` when it expands. References to `x` now become
references to that macro, and expanding them provides access to `τ`. The method
looks like something like this:

```racket
(let ([x- (attach-type-information (generate-temporary #'x) #'τ)])
  (let-syntax ([x (make-rename-transformer x-)])
    ... expand and check forms that may reference x ...))
```

The type `τ` is attached as [metadata][6] for a new identifier `x-`, which is
what `x` will transform to at any reference site. In order for this to work,
`x-` must be distinct from `x`. While it is possible to define `x` as a macro
that expands to `x` plus type information, it's a bit tricky to retrieve type
information from an infinite loop.

## What's an Idiom?

There's only one problem. We can't write typed functions the way we're used to
writing them in Racket! While we can easily extend our language with `let`,
[idiomatic][8] Racket binds intermediate values using `define`. To borrow from a
[recent example on the Racket Users mailing list][7], we're stuck writing
programs that look like

```racket
(let ([get-data (λ ([input : String])
                  (let ([url (construct-url input)])
                    (call/input-url url get-pure-port read-json)))])
  ... use get-data ...)
```

rather than

```racket
(define (get-data ([input : String]) 
  (define url (construct-url input)) 
  (call/input-url url get-pure-port read-json)) 
```

At first glance, the issue seems to be that the definition of `λ`
above limits the body to be a single expression when what we want to put there is
a sequence of definitions and expressions. To reach our goal, we need to change
the definition of `λ` to allow its body to be a sequence and then add `define`
to the language.

## Sequences

The first step is to create a typed form for sequences of definitions and
expressions, which can then be used by rules like `λ`:

```racket
(define-typed-syntax (begin e ...+) ≫
  [⊢ e ≫ e- ⇒ τ] ...
  #:with τ-final (stx-last #'(τ ...))
  -----------------------------------
  [⊢ (begin- e- ...) ⇒ τ-final])
```

This directs type checking to:

1. Check each `e` in the sequence individually, obtaining an expanded `e-` and
   inferred type `τ` for each.
2. Take the last type in the sequence and call it `τ-final`; Turnstile allows
   using `syntax-parse` directives such as `#:with` as premises.
3. Expand to Racket's `begin` (with the usual `-` suffix) and give the whole
   expression the type of the last expression.
   
Now, we can use `begin` in a revised definition of `λ`. The new rule takes a
non-empty squence of forms in the body and wraps them in our new `begin` form
for typechecking.

```racket
(define-typed-syntax (λ ([x:id (~datum :) τ_in:type] ...) e ...+) ≫
  [[x ≫ x- : τ_in.norm] ... ⊢ (begin e ...) ≫ e- ⇒ τ_out]
  -------------------------------------------------
  [⊢ (#%plain-lambda- (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)])
```

Now we need a way to include definitions in these sequences and we're set!

## The Problem With Define

Consulting the [Turnstile examples][9], we might end up with something like this:

```racket
(define-base-type Void)
(define- a-deep-dark-void (#%app- void-))
(define-typed-syntax define
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with x- (generate-temporary #'x)
   -----------------------------------------------------
   [⊢ (begin-
        (define-typed-variable-rename x ≫ x- : τ)
        (define- x- e-)
        a-deep-dark-void)
      ⇒ Void]]
  [(_ (f [x (~datum :) τ] ...) e ...+) ≫
   -----------------------------------
   [≻ (define f (λ ([x : τ] ...) e ...))]])
```

Let's break it down.

1. Create a new type, `Void`, to assign definitions.
2. Create a constant to serve as the canonical value of type `Void`.
3. Define a new typed form, `define`, given by two cases.
4. The first case matches `(define x e)`.
5. For those cases, check the type of the expression `e`, getting its
   expansion `e-` and type `τ`.
6. Create a new name, `x-`.
7. Expand to Racket's `begin`. Unlike `let`, `begin` does not create a new
   scope; definitions inside a `begin` are also visible in the surrounding
   context. That behavior is needed for scenarios like this one that expand to
   multiple definitions.
8. Turnstile provides `define-typed-variable-rename` which defines a macro that
   renames `x` to `x-` in the same manner that we saw above. By using a
   define-like form, the macro has the same scoping rules as `define`, so it
   will apply to references to `x` in the surround context---exactly what we
   want.
9. Define `x-` to refer to the supplied expression. Note that here `define-` is
   Racket's `define`.
10. Keep the result of evaluating this form in line with the type by yielding a
   value of type `Void`.
11. The second case allows for function definitions by rewriting to a term that
    matches the pattern for the first case.
    
Unfortunately, while this `define` will allow us to write module-level
definitions, using it in the body of a function causes an error:

```racket
(define (add2 [x : Int])
  (define almost (+ x 1))
  (+ almost 1))
==> almost: unbound identifier...
```

Pointing to the reference on the third line. The problem is that our `define`
and `begin` forms are not interacting in the way we might have hoped.

When we expand the body of the function above, we associate `x` with type `Int`
then start checking the body, wrapped in a `begin`:

```racket
(begin
  (define almost (+ x 1))
  (+ almost 1))
```

Consulting the definition of `begin`, we see that it checks/expands each
sub-expression in seqence. First in the sequence is a use of `define`, yielding

```
(begin-
  (define-syntax almost ...)
  (define- almost- ...)
  a-deep-dark-void)
```

Next, it turns to checking/expanding the subsequent `(+ almost 1)`, where it
will encounter the identifier `almost`. Even though our `define` formed produced
a binding for `almost` as part of its output, the expander hasn't actually
analyzed that binding by the time it reaches the reference in the next
expression.

The problem is a symptom of analyzing the sequence of forms using an ellipses,
which corresponds to mapping the typechecking/expanding process over each
individually. The mapping operation stipulates that checking each item is
independent of checking the others. But, when we add `define` to the
language, that is no longer the case. A definition form influences how we
typecheck its neighbors by introducing a new name and its type. This information
must be communicated to the following forms in order to properly check
references. Unfortunately, Turnstile doesn't provide a way of threading binding
information through the checking of a sequnce of typed forms. We're going to
need to implement our own solution, requiring us to dive underneath the
abstractions provided by Turnstile and get intimate with Racket's syntax model.

## Internal Definition Contexts

In order for `(+ almost 1)` to succesfully typecheck/expand, we need to be able
to associate `almost` with a suitable type. Turnstile provides a way to set up
such an association, but as we saw before, Turnstile's interface doesn't suit
this scenario.

[Internal definition contexts][10] are among the host of tools Racket provides
for manipulating and transforming syntax. When using `local-expand`, we can
optionally pass in a definition context containing binding information. If we
create a definition context for the body of the function, extending it for each
definition, then `local-expand`-ing references such as the above one should work
out. Normally, Turnstile calls `local-expand` internally in accordance with the
type rules we write down, but in order to use our own definition context we're
going to have to call it ourselves.

We can create a definition context with [`syntax-local-make-definition-context`][10], as in

```racket
(define def-ctx (syntax-local-make-definition-context))
```

And then (imperatively) add bindings to `def-ctx` with
[`syntax-local-bind-syntaxes`][11]. The first argument is a list of identifiers
to bind; we will only be binding one identifier at a time, consequently only
passing singleton lists. The second argument dictates what the given identifier
*means*. Passing `#f` corresponds to a run-time/phase 0 binding, such as that of
a procedure argument, `let`, or `define`; alternatively, we can provide syntax
that evaluates to a function, establishing a transformer binding invoked on
references to the identifier. Using both modes, we can define a function that
sets up a Turnstile-style type rename:

```racket
(define-for-syntax (int-def-ctx-bind-type-rename x x- t ctx)
  (syntax-local-bind-syntaxes (list x)
                              #`(make-rename-transformer
                                 (add-orig (assign-type #'#,x- #'#,t #:wrap? #f) #'#,x))
                              ctx)
  (syntax-local-bind-syntaxes (list x-) #f ctx))
```

The first call binds `x` to a transformer that renames to `x-`; the second lets
the expander know that we are taking care of making sure that `x-` will actually
be bound to something.

Our `define` form must communicate the information needed to call
`int-def-ctx-bind-type-rename` back out to the surrounding context. One way to
do this is to add an intermediate step to the expansion of `define` that
includes the necessary information as part of its syntax. Then, the surrounding
context can analyze the expansion of each term, looking for that form.

Concretely, `define` will expand to `define/intermediate`, which will in turn
expand to what `define` originally expanded to:

```racket
(define-typed-syntax define
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with x- (generate-temporary #'x)
   #:with x+ (syntax-local-identifier-as-binding #'x)
   -----------------------------------------------------
   [⊢ (define/intermediate x+ x- τ e-) ⇒ Void]]
  [(_ (f [x (~datum :) τ] ...) e ...+) ≫
   -----------------------------------
   [≻ (define f (λ+ ([x : τ] ...) e ...))]])         

(define-syntax (define/intermediate stx)
  (syntax-parse stx
    [(_ x:id x-:id τ e)
     #'(begin-
         (define-typed-variable-rename x ≫ x- : τ)
         (define- x- e)
         a-deep-dark-void)]))
```

The reason we create an `x+` using [`syntax-local-identifier-as-binding`][13] is
[due to a bug in the expander][12]. The explanation is rather involved and
frankly I only barely understand what's going on myself (if at all), so let's
just leave it at that and move on.

Then, for each form `e` in a sequence, we can call `local-expand` with `def-ctx`
and then check the expansion, `e-`, for `define/intermediate`. In those cases,
we can use `int-def-ctx-bind-type-rename` to add it to the context. The
procedure `add-bindings-to-ctx` performs this check on an expanded form `e-`:

```racket
(define-for-syntax (add-bindings-to-ctx e- def-ctx)
  (syntax-parse e-
        #:literals (erased define/intermediate)
        [(erased (define/intermediate x:id x-:id τ e-))
         (int-def-ctx-bind-type-rename #'x #'x- #'τ def-ctx)]
        [_ (void)]))
        
```

One extra detail that snuck in to the implementation is the presence of the
`erased` tag. `erased` is a macro inserted by Turnstile that serves to mark
language forms that have already been expanded, helping control what expands
when. Since we used `define-typed-syntax` for our `define`, Turnstile wraps the
output with `erased`.

We now have the key ingredients to define a procedure, `walk/bind` that will
serve as the primary vehicle to perform type checking of a sequence of forms,
threading binding information through using a definition context. Processing
sequences of defintions and expressions will iterate through them one at a time,
and for each form `e`:

- `local-expand` `e` using our internal definition context, resulting in an `e-`.
- Retrieve the type of `e` from the metadata of `e-` using Turnstile's `typeof` helper.
- Check if `e` defined a binding, in which case add it to the context.

Aggregating the expanded syntax and type of each form as we go along, we get

```racket
(define-for-syntax (walk/bind e...)
  (define def-ctx (syntax-local-make-definition-context))
  (define unique (gensym 'walk/bind))
  (define-values (rev-e-... rev-τ...)
    (for/fold ([rev-e-... '()]
               [rev-τ... '()])
              ([e (in-syntax e...)])
      (define e- (local-expand e (list unique) (list #'erased) def-ctx))
      (define τ (typeof e-))
      (add-bindings-to-ctx e- def-ctx)
      (values (cons e- rev-e-...)
              (cons τ rev-τ...))))
  (values (reverse rev-e-...)
          (reverse rev-τ...)))
```

The value `unique` and its use as an argument is dictated by the documentation
of `local-expand`: "For a particular internal-definition context, generate a
unique value and put it into a list for context-v." By using `#'erased` in the
stop list for `local-expand`, we stop expansion at the same points that Turnstile
does.

Now we can use `walk/bind` to implement `begin`:

```racket
(define-typed-syntax (begin e ...+) ≫
  #:do [(define-values (e-... τ...) (walk/bind #'(e ...)))]
  #:with τ-final (last τ...)
  --------------------
  [⊢ (begin- #,@e-...) ⇒ τ-final])
```

and voilà!

```racket
(define (add2 [x : Int])
  (define almost (+ x 1))
  (+ almost 1))

(add2 3)
;;=> 5
```

# But Wait, There's More

I believe this design is can be dropped in 'as-is' and with a few extensions be
useful for a wide variety of Turnstile languages. However, there are a few
shortcomings (that I am aware of) that I will leave as exercises for the
interested reader:

- The implementation of `define` doesn't allow recursive functions.
- Language extensibility; macros that expand to multiple uses of `define` inside
  a `begin` won't work (why not?), such as

```racket
(define-syntax (define/memo stx)
  (syntax-parse stx
    [(_ (f [x (~datum :) τ] ...) e ...+)
     #'(begin
         (define memo ... memo table ...)
         (define (f [x : τ] ...)
           ... check memo table ...
           e ...))]))
```


<!-- References -->

[1]: http://docs.racket-lang.org/turnstile/The_Turnstile_Guide.html
[2]: http://racket-lang.org/
[3]: http://www.ccs.neu.edu/home/stchang/pubs/ckg-popl2017.pdf
[4]: http://docs.racket-lang.org/syntax/stxparse.html
[5]: http://docs.racket-lang.org/reference/lambda.html?q=%23%25plain-lambda#%28form._%28%28lib._racket%2Fprivate%2Fbase..rkt%29._~23~25plain-lambda%29%29
[6]: http://docs.racket-lang.org/reference/stxprops.html
[7]: https://groups.google.com/forum/#!topic/racket-users/LE66fKtcJMs
[8]: https://docs.racket-lang.org/style/Choosing_the_Right_Construct.html#%28part._.Definitions%29
[9]: https://github.com/stchang/macrotypes/blob/c5b663f7e663c564cb2baf0e0a352d5fde4d2bd7/turnstile/examples/ext-stlc.rkt#L55
[10]: http://docs.racket-lang.org/reference/stxtrans.html#%28def._%28%28quote._~23~25kernel%29._syntax-local-make-definition-context%29%29
[11]: http://docs.racket-lang.org/reference/stxtrans.html#%28def._%28%28quote._~23~25kernel%29._syntax-local-bind-syntaxes%29%29
[12]: https://github.com/racket/racket/pull/2237
[13]: http://docs.racket-lang.org/reference/stxtrans.html#%28def._%28%28quote._~23~25kernel%29._syntax-local-identifier-as-binding%29%29
[14]: https://gist.github.com/howell/e2d4501e24db503e4cd9aa368172a502
