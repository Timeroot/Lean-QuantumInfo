\section{Lieb and Ando theorem}

Throughout this section, let $\mathcal H$ be a finite-dimensional complex Hilbert space, and put
\[
  \mathcal P(\mathcal H):=B(\mathcal H)_{++}.
\]

Kubo and Ando~\cite{8} defined the operator $\alpha$-power mean (or $\alpha$-geometric mean) on $\mathcal P(\mathcal H)$, for $0\le \alpha\le 1$, by
\[
  A\#_{\alpha}B
  :=A^{1/2}\left(A^{-1/2}BA^{-1/2}\right)^{\alpha}A^{1/2}.
\]

We introduce the operator $(\alpha,\beta)$-power mean as a generalization of the operator $\alpha$-power mean, for $0\le \alpha\le 2$ and $0\le \beta\le 1$, by
\[
  A\#_{(\alpha,\beta)}B
  :=A^{\beta/2}\left(A^{-\beta/2}BA^{-\beta/2}\right)^{\alpha}A^{\beta/2}.
\]
It is clear that every operator $(\alpha,1)$-power mean is an operator $\alpha$-power mean.

\textbf{Theorem 1.1.}
For $A,B\in\mathcal P(\mathcal H)$, the operator $(\alpha,\beta)$-power mean is jointly concave in the Löwner order for $0\le \alpha,\beta\le 1$, and jointly convex in the Löwner order for $1\le \alpha\le 2$ and $0\le \beta\le 1$.

\textit{Proof.}
Let $f(t)=t^{\alpha}$ and $h(t)=t^{\beta}$. Then
\[
  A\#_{(\alpha,\beta)}B=(f\triangle h)(A,B)
\]
(see~\cite{4}). For $0\le \alpha,\beta\le 1$, the result follows from the concavity of $f,h$ and Corollary 2.6(i) of~\cite{4}. For $1\le \alpha\le 2$ and $0\le \beta\le 1$, the result follows from the convexity of $f$, the concavity of $h$, and Theorem 2.5 of~\cite{4}. $\square$

Equip $B(\mathcal H)$ with the Hilbert--Schmidt inner product
\[
  \langle X,Y\rangle_{\mathrm{HS}}:=\operatorname{Tr}(XY^*).
\]
For $A,B\in\mathcal P(\mathcal H)$, define $L_A(X):=AX$ and $R_B(X):=XB$ on $B(\mathcal H)$. Then $L_A$ and $R_B$ are commuting strictly positive operators on the Hilbert space $B(\mathcal H)$. Fix $K\in B(\mathcal H)$ and define
\[
  \Phi_K(T):=\langle T(K^*),K^*\rangle_{\mathrm{HS}}=\operatorname{Tr}\bigl(T(K^*)K\bigr),
  \qquad T\in B\bigl(B(\mathcal H)\bigr).
\]
If $T\ge 0$ on $B(\mathcal H)$, then $\Phi_K(T)\ge 0$; hence $\Phi_K$ is a positive linear functional.

\textbf{Theorem 1.2.}
\begin{enumerate}
  \item[(a)] (Lieb's theorem) If $0<s<1$, then
  \[
    F(A,B)=\operatorname{Tr}\bigl(A^sK^*B^{1-s}K\bigr)
  \]
  is jointly concave on $\mathcal P(\mathcal H)\times \mathcal P(\mathcal H)$.

  \item[(b)] (Lieb's extension theorem) Suppose $p,q>0$ and $p+q\le 1$. Then
  \[
    (A,B)\mapsto\operatorname{Tr}\bigl(A^qK^*B^pK\bigr)
  \]
  is jointly concave on $\mathcal P(\mathcal H)\times \mathcal P(\mathcal H)$.
\end{enumerate}

\textit{Proof.}
\begin{enumerate}
  \item[(a)] Since $L_A$ and $R_B$ commute, functional calculus for commuting positive operators gives
  \[
    R_B\#_{(s,1)}L_A
    =R_B^{1/2}\bigl(R_B^{-1/2}L_A R_B^{-1/2}\bigr)^sR_B^{1/2}
    =L_A^sR_B^{1-s}.
  \]
  Hence
  \[
    \bigl(R_B\#_{(s,1)}L_A\bigr)(K^*)=A^sK^*B^{1-s},
  \]
  and therefore
  \[
    \Phi_K\bigl(R_B\#_{(s,1)}L_A\bigr)
    =\operatorname{Tr}\bigl(A^sK^*B^{1-s}K\bigr).
  \]
  By Theorem 1.1 with $(\alpha,\beta)=(s,1)$, $(A,B)\mapsto R_B\#_{(s,1)}L_A$ is jointly concave in the Löwner order. Applying the positive linear functional $\Phi_K$ yields the joint concavity of $F$.

  \item[(b)] Since $p>0$ and $p+q\le 1$, we have $q<1$. Put $\beta=\frac{p}{1-q}\in(0,1]$. Again using commutativity,
  \[
    R_B\#_{(q,\beta)}L_A
    =R_B^{\beta/2}\bigl(R_B^{-\beta/2}L_A R_B^{-\beta/2}\bigr)^qR_B^{\beta/2}
    =L_A^qR_B^{\beta(1-q)}
    =L_A^qR_B^p,
  \]
  hence
  \[
    \Phi_K\Bigl(R_B\#_{\left(q,\frac{p}{1-q}\right)}L_A\Bigr)
    =\operatorname{Tr}\bigl(A^qK^*B^pK\bigr).
  \]
  Because $0<q<1$ and $0<\beta\le 1$, Theorem 1.1 implies that $(A,B)\mapsto R_B\#_{(q,\beta)}L_A$ is jointly concave. Applying $\Phi_K$ gives the desired joint concavity. $\square$
\end{enumerate}

\textbf{Corollary 1.3.}
The function
\[
  (A,B)\mapsto\operatorname{Tr}\bigl(A^qK^*B^{1-r}K\bigr)
\]
is jointly convex on $\mathcal P(\mathcal H)\times \mathcal P(\mathcal H)$ when $1<r\le q\le 2$.

\textit{Proof.}
Put $\beta=\frac{1-r}{1-q}\in[0,1]$. Since $L_A$ and $R_B$ commute,
\[
  R_B\#_{(q,\beta)}L_A=L_A^qR_B^{1-r}.
\]
Hence
\[
  \Phi_K\Bigl(R_B\#_{\left(q,\frac{1-r}{1-q}\right)}L_A\Bigr)
  =\operatorname{Tr}\bigl(A^qK^*B^{1-r}K\bigr).
\]
Since $1\le q\le 2$ and $0\le \beta\le 1$, Theorem 1.1 yields joint convexity of $(A,B)\mapsto R_B\#_{(q,\beta)}L_A$, and hence of the traced function.
$\square$

A significant complement of Lieb's concavity theorem is the following theorem, following Ando's proof~\cite{1}.

\textbf{Theorem 1.4 (Ando's convexity theorem).}
Suppose that $1\le q\le 2$ and $0\le r\le 1$ with $q-r\ge 1$. Then
\[
  (A,B)\mapsto\operatorname{Tr}\bigl(A^qK^*B^{-r}K\bigr)
\]
is jointly convex on $\mathcal P(\mathcal H)\times \mathcal P(\mathcal H)$.

\textit{Proof.}
If $q=1$, then $q-r\ge 1$ implies $r=0$, and
\[
  (A,B)\mapsto\operatorname{Tr}(AK^*K)
\]
is affine in $A$ (and independent of $B$), hence jointly convex.

Assume now $q>1$, and put $\beta=\frac{r}{q-1}\in[0,1]$. Since $L_A$ and $R_B$ commute,
\[
  R_B\#_{(q,\beta)}L_A=L_A^qR_B^{-r}.
\]
Hence
\[
  \Phi_K\Bigl(R_B\#_{\left(q,\frac{r}{q-1}\right)}L_A\Bigr)
  =\operatorname{Tr}\bigl(A^qK^*B^{-r}K\bigr).
\]
The result follows from Theorem 1.1 in the convex range $1\le q\le 2$, $0\le \beta\le 1$, together with positivity of $\Phi_K$. $\square$
