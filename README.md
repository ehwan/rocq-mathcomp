# rocq-mathcomp-numerical-analysis

This project formalizes results in numerical analysis using Rocq and MathComp Analysis.

## Taylor polynomials · [taylor_poly.v](taylor_poly.v)

Fix a real function $f$ and an expansion center $a$. Write $f^{(i)}$ for the $i$th derivative, with $f^{(0)}=f$. The center stays fixed when differentiating with respect to $x$.

| Definition | Notation | Formula |
| --- | --- | --- |
| `taylor_term (R : realType) (f : R -> R) (i : nat) (a : R)` | $t_i[f]$ | $x \mapsto \dfrac{f^{(i)}(a)}{i!}(x-a)^i$ |
| `taylor_sum (R : realType) (f : R -> R) (n : nat) (a : R)` | $T_n[f]$ | $x \mapsto \displaystyle\sum_{i=0}^{n}t_i[f](x)$ |

| Lemma | Statement |
| --- | --- |
| `taylor_term_derivable`, `taylor_sum_derivable` | Both $t_n[f]$ and $T_n[f]$ are differentiable at every $x$. |
| `taylor_term0`, `taylor_sum0` | $t_0[f](x)=T_0[f](x)=f(a)$ |
| `taylor_term_centerS`, `taylor_sum_center` | At the center, $t_{n+1}[f](a)=0$ and $T_n[f](a)=f(a)$. |
| `taylor_sumS` | $T_{n+1}[f](x)=T_n[f](x)+t_{n+1}[f](x)$ |
| `derive_taylor_term0`, `derive_taylor_sum0` | $\dfrac{d}{dx}t_0[f](x)=\dfrac{d}{dx}T_0[f](x)=0$ |
| `derive_taylor_termS` | $\dfrac{d}{dx}t_{n+1}[f](x)=t_n[f'](x)$ |
| `derive_taylor_sumS` | $\dfrac{d}{dx}T_{n+1}[f](x)=T_n[f'](x)$ |

## Peano remainder · [taylor.v](taylor.v)

`taylor_theorem` · [Taylor's theorem in one real variable](https://en.wikipedia.org/wiki/Taylor%27s_theorem#Statement_of_the_theorem)

$$
\lim_{x\to a}\frac{f(x)-T_k[f](x)}{(x-a)^k}=0.
$$

## Lagrange remainder · [taylor_expansion.v](taylor_expansion.v)

$a, x \in I$ for some interval $I$.

`taylor_expansion_lagrange`

$$
\exists\,\xi\in I,\qquad f(x)=T_n[f](x)+\frac{f^{(n+1)}(\xi)}{(n+1)!}(x-a)^{n+1}.
$$

`taylor_expansion_bound` · $M$ is an upper bound for $\lvert f^{(n+1)}\rvert$ on $I$.

$$
\bigl\lvert f(x)-T_n[f](x)\bigr\rvert\le\frac{M}{(n+1)!}\lvert x-a\rvert^{n+1}.
$$

## License

This project uses [CeCILL-C](LICENSE), the same license as [MathComp Analysis](https://github.com/math-comp/analysis/blob/master/LICENCE).
