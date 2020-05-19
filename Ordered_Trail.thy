(*<*)theory Ordered_Trail 
  imports
    Graph_Theory.Bidirected_Digraph
    Graph_Theory.Weighted_Graph
    Graph_Theory.Kuratowski
    Graph_Theory.Arc_Walk
begin(*>*)

section "Introduction"

text \<open> 

The problem of finding a longest trail with strictly increasing or strictly decreasing weights in
an edge-weighted graph is an interesting graph theoretic problem~\cite{graham1973increasing,calderbank1984increasing,yuster2001large,de2015increasing}, 
with potential
applications to scheduling and cost distribution in traffic planning and routing~\cite{byron}.
In this paper, we formalize and automate the reasoning about
strictly-ordered trail properties by developing an extendable flexible library in the proof assistant Isabelle/HOL~\cite{nipkow2002isabelle}.

As a motivating example consider the following (undirected) graph $K_4$, where each edge is annotated 
with a different integer-valued weight ranging from $1, \ldots, 6$:

\begin{figure}
\centering
		\begin{tikzpicture}
		\node[draw,circle] at (0, 0) (a) {$v_1$};
		\node[draw,circle] at (5, 0) (b) {$v_2$};
	
		\node[draw,circle] at (0, -3) (c) {$v_3$};
		\node[draw,circle] at (5, -3) (d) {$v_4$};
		
		% draw edges
		\draw[] (a) -- (b)  node[above,midway] {$1$};
		\draw[] (a) -- (c)  node[midway, left] {$3$};
		\draw[] (a) -- (d)  node[near start, above] {$6$};
	  
    \draw[] (b) -- (c)  node[near start, above] {$5$};
		\draw[] (b) -- (d)  node[near start, right] {$4$};
		
		\draw[] (c) -- (d)  node[midway, above] {$2$};
		\end{tikzpicture}
  \caption{Example graph $\protect K_4$}\label{exampleGraph}
\end{figure}

\noindent When considering $K_4$, the question we address in this paper is whether $K_4$ has a 
strictly decreasing trail of length $k\geq 1$. A trail is a sequence of edges in which both endpoints of 
an edge are incident to a different direct neighbor's endpoint in that sequence.
Moreover, our work provides a formally verified algorithm 
computing such trails. Note that there is a decreasing trail in $K_4$ starting at vertex $v_3$, 
with trail length 3; namely $(v_3v_2; v_2v_4; v_4v_3)$ is such a trail, with each edge in the trail having 
a higher weight than its consecutive edge in the trail. Similarly, $K_4$ has decreasing trails of 
length 3 starting from $v_1$, $v_2$, and $v_4$ respectively. A natural question to ask,
which we address in this paper, is whether it is possible to construct a graph such that the 
 constructed graph has 4 vertices and 5 edges, and no vertex is the starting node of a trail of 
length 3? We answer this question negatively, in an even more general setting,  not restricted to 4 
vertices and 5 edges. Similarly to the theoretical results of~\cite{graham1973increasing}, we show 
that, given a graph $G$ with $n$ vertices and $q$ edges, there is always a strictly decreasing trail of length at least
$2 \cdot \lfloor\frac{q}{n}\rfloor$. While such a graph theoretical result has already been announced 
\cite{graham1973increasing}, in this paper we formalize the results in Isabelle/HOL and construct 
a Isabelle/HOL-verified algorithm computing strictly decreasing trails of length $k$, whenever such trails exist.

Let us note that proving that a
 graph $G$ with $n$ vertices and $q$ edges has/does not have decreasing trails is possible for small 
$n$, using automated reasoning engines such as Vampire~\cite{Vampire13} and Z3~\cite{de2008z3}. 
One can restrict the weights to the integers $1,..,q$ and since $q \le {n \choose 2}$ there is a 
finite number of possibilities for each n. 
Nevertheless, the limit of such an undertaking is
reached soon. On our machine\footnote{standard laptop with
1.7 GHz Dual-Core Intel Core i5 and  8 GB 1600 MHz memory} even for n = 7, both Vampire and Z3 fail 
proving the existence of strictly decreasing trails, using a 1 hour time limit. This
is due to the fact that every combination of edge weights and starting nodes is
tested to be a solution. Thus, the provers are not able to contribute to the process of finding an 
effective proof of the statement. Even for relatively small numbers $n$, our experiments show that 
state-of-the-art automated  provers are not able to prove whether weighted graphs have a strictly decreasing trail 
of a certain length.

We also note that this limitation goes beyond automated provers. In the Isabelle proof assistant, 
proving that a complete graph with 3 vertices, i.e. $K_3$,  will
always contain a strictly decreasing trail of length 3 is quite exhaustive, as it requires reasoning about 3! = 6 possibilities
for a distribution of a weight function $w$ and then manually constructing concrete trails:

\begin{center}
@{text "w(v\<^sub>1,v\<^sub>2) = 2 \<and> w(v\<^sub>2,v\<^sub>3) = 1 \<and> w(v\<^sub>3,v\<^sub>1) = 3"} 

@{text "\<longrightarrow> incTrail K\<^sub>3 w [(v\<^sub>3,v\<^sub>2),(v\<^sub>2,v\<^sub>1),(v\<^sub>1,v\<^sub>3)]"}
\end{center}

Based on such limitations of automative and interactive provers, in this paper we aim at formalizing 
and proving existence of trails of length $n$, where $n\geq 1$ is a symbolic constant. As such, 
proving for example that graphs have trails of length $4$, for a concrete $n$,  become instances 
of our approach. To this end, we build upon existing works in this area. In particular, the first 
to raise the question of the minimum length of strictly increasing
trails of arbitrary graphs  were Chv\'atal and Koml\'os~\cite{chvatal1970some}. Subsequently, 
Graham and Kletman~\cite{graham1973increasing} proved that the lower bound of the length of increasing trails 
is given by $2 \cdot \lfloor\frac{q}{n}\rfloor$, as also mentioned above. In our work, we formalize and verify 
such results in Isabelle/HOL. Yet, our work is not a straightforward adaptation and formalization   
of Graham and Kletman's proof~\cite{graham1973increasing}. Rather, we focus on decreasing trails instead of increasing trails 
and give an algorithm computing longest decreasing trails of a given graph (Algorithm \ref{algo}).  
By formalizing Algorithm \ref{algo} in Isabelle/HOL, we also formally verify the correctness 
of the trails computed by our approach. Moreover, we prove that any strictly decreasing trail is also an strictly increasing 
one, allowing this way to use our formalization in Isabelle/HOL also to formalize results of Graham and Kletman~\cite{graham1973increasing}.

\noindent\paragraph{\bf Contributions.} This paper brings the following contributions.
\begin{description}
\item[(1)]
We formalize strictly increasing trails and provide basic lemmas about their
properties.
\item[(2)] We formalize strictly decreasing trails, in addition to the increasing trail setting of~\cite{graham1973increasing}. 
We prove the duality between strictly increasing and strictly decreasing trails, that is, any such decreasing trail is an increasing one, and vice versa.
\item[(3)] We design an algorithm computing longest ordered paths (Algorithm \ref{algo}), and formally verify  its correctness in Isabelle/HOL.
We extract our algorithm to Haskell program code using Isabelle's program extraction tool. Thus, we obtain a fully verified algorithm to compute the length
of strictly-ordered trails in any given graph and weight distribution.
\item[(4)] We
verify the lower bound on
the minimum length of strictly decreasing trails of arbitrary graphs, and of complete graphs in particular.
\item[(5)] We build upon the Graph-Theory library by Noschinski~\cite{Graph_Theory-AFP},  that is part of the
Archive of Formal Proofs (AFP) and already includes many results on walks and
general properties of graphs. We introduce the digital dataset {\it v} formalizing properties of graph trails. Our dataset  consists of
$\sim$2000 lines of Isabelle code and it took about one month for one person to finish. As far as we know this is the first formalization of
ordered trails in a proof assistant.
\end{description}

This paper was generated from Isabelle/HOL source code using Isabelle's document preparation tool 
and is therefore fully verified. The source code is available
online at \url{https://github.com/Lachnitt/Ordered_Trail}. The rest of the paper is organized as follows.
Section 2 recalls basic terminology and properties from graph theory. 
We prove lower bounds on strictly increasing/decreasing trails in Section 3. We describe our Isabelle/HOL 
formalization in Isabelle/HOL in Section 4. We discuss further directions in Section 5 and conclude our paper with Section 6.
 \<close>

section "Preliminaries" 
text \<open> \label{Prelim}
We briefly recapitulate the basic notions of graph theory. A {\em graph} $G = (V,E)$ consists of
a set $V$ of {\em vertices} and a set $E \subseteq V \times V$ of {\em edges}. A graph is undirected 
if $(v_1,v_2)\in E$ implies that also $(v_2,v_1)\in E$. A graph is {\em complete}
 if every pair of vertices is connected by an edge. A graph is {\em loopfree} or {\em simple} if there are no edges $(x,x)\in E$ and 
{\em finite} if the number of vertices $|V|$ is finite. Finally, we call 
a graph $G'=(V',E')$ a {\em subgraph} of $G = (V,E) $ if $V' \subseteq V$ and $E' \subseteq E$.

If a graph is equipped with a
 weight function $w: E \mapsto \mathbb{R}$ that maps edges to real numbers, it is called 
 an {\em edge-weighted graph}. In the following, whenever a graph is mentioned it is implicitly assumed
that this graph comes equipped with a weight function. A vertex labelling is a function $L: V \mapsto \mathbb{N}$.

A {\em trail of length k} in a graph $G = (V,E)$ is a sequence $(e_1,\ldots,e_k)$, $e_i \in E$, of distinct edges such that
 there exists a corresponding sequence of vertices $(v_0,...,v_k)$ where $e_i = v_{i-1}v_i$. 
A {\em strictly decreasing trail} in an edge-weighted graph $G = (V,E)$ with weight function $w$
is a trail such that $w (e_i) > w (e_{i+1})$. Likewise, a {\em strictly increasing trail} is a trail such that $w (e_i) < w (e_{i+1})$.

We will denote the length of a longest strictly increasing trail with $P_i(w,G)$. Likewise we will denote the length
of a longest strictly decreasing trail with $P_d(w,G)$. In any undirected graph, it holds that $P_i(w,G) = P_d(w,G)$, 
a result that we will formally verify in Section \ref{trails}. 

Let $f_i(n) = \min P_i(w,K_n)$ denote the minimum length of an strictly increasing trail that must exist in 
the complete graph with $n$ vertices. Likewise, $f_d(n) = \min P_d(w,K_n)$ in the case that we consider 
strictly decreasing trails. \<close>

section "Lower Bounds on Increasing and Decreasing Trails in Weighted Graphs"

text \<open>\label{PaperProof}
The proof introduced in the following is based on similar ideas as in \cite{graham1973increasing}. 
However, we diverge from \cite{graham1973increasing} in several aspects. Firstly, we consider strictly decreasing instead of strictly increasing trails,
reducing the complexity of the automated proof (see Section \ref{Formalization}). 
Moreover, we add tighter bounds than necessary to give a fully constructive proof in terms of an algorithm for computing
the length of these trails (see Section \ref{localeSurjective}). We discuss this further at the end of the section.

We start by introducing the notion of a weighted subgraph and then we built on that by specifying a family of labelling functions:

\begin{definition}[Weighted Subgraph] \label{WeightedSG}
	Let $G=(V,E)$ be a graph with weight function $w:E\rightarrow \{1,\ldots,q\}$ where $|E| = q$.
	For each $i\in \{0,...,q\}$ define a weighted subgraph $G^i = (V,E^i)$ such that $e\in E^i$ iff $w(e)\in \{1,...,i\}$. 
  That is, $G^i$ contains only edges labelled with weights $\le i$.
\end{definition}

\begin{definition}[Labelling Function]\label{Labelling}
	For each $G^i=(V,E^i)$ we define $L^i:E^i\rightarrow \{1,\ldots,\frac{n(n-1)}{2}\}$ where $n = |V|$ a labelling function such 
that $L^i(v)$ is the length of a longest strictly decreasing trail starting at vertex v using only edges in $E^i$.
\end{definition}

\noindent In Figure \ref{exampleSubgraph} the example graph from Figure \ref{exampleGraph} is revisited to 
illustrate these definitions. We need to prove the following property.

\begin{figure}
\centering

	\begin{multicols}{2}[\columnsep2em] 

	\begin{tikzpicture}
	\node[draw,circle] at (0, 0)   (a) {$v_1$};
	\node[draw,circle] at (5, 0)   (b) {$v_2$};
	
	\node[draw,circle] at (0, -3)  (c)     {$v_3$};
	\node[draw,circle] at (5, -3)  (d)     {$v_4$};
	
	% draw edges
	\draw[] (a) -- (b)  node[above,midway] {$1$};
  \draw[] (a) -- (c)  node[midway, left] {$3$};
	\draw[] (b) -- (d)  node[midway, right] {$4$};
	
	\draw[] (b) -- (c)  node[midway, above] {$5$};
	\draw[] (c) -- (d)  node[midway, above] {$2$};
	
	\end{tikzpicture}\\
		\columnbreak
		\vspace{7cm}
		\ \\
		Decreasing trails from $v_3$ are: 
		
		$v_3-v_4$,  
		
		$v_3-v_1-v_2$, 
		
		$v_3-v_2-v_1$,
		
		$v_3-v_2-v_4-v3$
		
		Therefore, $L^5(v_3) = 3$\\ \ \\

		Decreasing trails from $v_1$ are:
		
		$v_1-v_2$
		
		$v_1-v_3-v_4$
		
		Therefore, $L^5(v_1) = 2$
	\end{multicols}
	
  \caption{Graph $G^5$ with labelling function $L^5$}\label{exampleSubgraph}
\end{figure}

\begin{lemma}\label{sum}
	Let $i < q$ and $G^i$ a labelled subgraph of G. Then, adding the edge labelled with $i+1$ to the 
graph $G_i$ increases the sum of the lengths of strictly decreasing trails at least by 2, i.e.,
	$\sum_{v\in V} L^{i+1}(v) \ge \sum_{v\in V} L^{i}(v)+2$.
\end{lemma}
\vspace{-1em}
\begin{proof}
Let $e$ be the edge labelled with $i+1$ and denote its endpoints with $u_1$ and $u_2$. It holds that $E^i \cup \{e\} = E^{i+1}$, 
therefore the graph $G^{i+1}$ is $G^i$ with the additional edge $e$. As $w(e') < w(e) $, for all $e' \in E^i$ we have 
 $L^{i+1}(v) = L^i(v)$ for all $v\in V$ with $u_1\neq v, u_2\neq v$. It also holds that $L^{i+1}(u_1) = \max(L^i(u_2)+1,L^i(u_1))$ 
because either that longest trail from $u_1$ can be prolonged with edge $e$ ($i+1$ will be greater than the weight of the first edge 
in this trail by construction of $L^{i+1}$) or there is already a longer trail starting from $u_1$ not using e. 
We derive $L^{i+1}(u_2) = \max(L^i(u_1)+1,L^i(u_2))$ based on a similar reasoning. See Figure \ref{cases} for a visualisation. 

Note that $L^{i+1}(v) = L^i(v)$ for $v\in V \setminus \{u_1,u_2\}$, because no edge incident to these vertices was added and
a trail starting from them cannot be prolonged since the new edge has bigger weight than any edge in such a 
trail.

If $L(u_1)=L(u_2)$, then $L^{i+1}(u_1) = L^i(u_1) + 1$ and $L^{i+1}(u_2) = L^i(u_2)+1$ and thus the sum increases exactly by 2. 
If $L(u_1)>L(u_2)$ then $L^{i+1}(u_2) = L^i(u_1) +1 \ge L^i(u_2)+2$, otherwise $L^{i+1}(u_1) = L^i(u_2) +1 \ge L^i(u_1)+2$. Thus, 

\begin{flalign*}
&\sum_{v\in V} L^{i+1}(v) \\
= &\sum_{v\in (V-\{u_1,u_2\})} L^{i+1}(v)+L^{i+1}(u_1)+L^{i+1}(u_2)\\
\ge & \sum_{v\in (V-\{u_1,u_2\})} L^{i+1}(v)+L^i(u_1)+L^i(u_2)+2\\
= & \sum_{v\in V} L^{i}(v)+2.
\end{flalign*}\\

\end{proof}

\begin{figure}[h]
	\centering
	\begin{tikzpicture}
	\node at (-4, 6)  {Situation before adding edge $e$: }; 
	\node[draw,circle, label = $L^i(u_1)$] at (0, 6)   (a) {};
	\node[draw,circle, label = $L^i(u_2)$] at (4, 6)   (b) {};
	
	\node at (-4.5, 4)  {Case 1: $L^i(u_1) = L^i(u_2)$: }; 
	\node[draw,circle, label = $L^{i+1}(u_1)+1$] at (0, 4)   (c) {};
	\node[draw,circle, label = $L^{i+1}(u_2)+1$] at (4, 4)   (d) {};			
	\draw[] (c) -- (d)  node[below,midway] {$i+1$};
	
	\node at (-4.5, 2)  {Case 2: $L^i(u_1) > L^i(u_2)$:  }; 
	\node[draw,circle, label = $L^{i+1}(u_2)+1$] at (0, 2)   (c) {};
	\node[draw,circle, label = $L^{i+1}(u_2)$] at (4, 2)   (d) {};			
	\draw[] (c) -- (d)  node[below,midway] {$i+1$};
	
	\node at (-4.5, 0)  {Case 3: $L^i(u_1) < L^i(u_2)$:}; 
	\node[draw,circle, label = $L^{i+1}(u_1)$] at (0, 0)   (c) {};
	\node[draw,circle, label = $L^{i+1}(u_1)+1$] at (4, 0)   (d) {};			
	\draw[] (c) -- (d)  node[below,midway] {$i+1$};
	\end{tikzpicture}
	\caption{Case distinction when adding edge $e$ in Lemma \ref{sum}}\label{cases}
\end{figure}
			

\noindent Note that the proof of Lemma \ref{sum} is constructive, yielding the Algorithm \ref{algo} for computing
longest strictly decreasing trails. Function $findEndpoints$ searches for an edge in a graph $G$ by its weight $i$ and returns
both endpoints. Function $findMax$ returns the maximum value of the array $L$. 

\begin{algorithm}[H]
	\SetAlgoLined
	
	\For{$v\in V$}{$L(v):=0$}
	\For{$i=1; i<|E|; i++$}{
		$(u,v) = findEndpoints(G,i)$\;
		$temp = L(u)$\;
		$L(u) = \max(L(v)+1,L(u))$ \;
		$L(v) = \max(temp+1,L(v))$ \;	
	}

	return findMax(L)\;

\caption{Find Longest Strictly Decreasing Trail}\label{algo}
\end{algorithm}

\begin{lemma}$\sum_{v\in V} L^{q}(v) \ge 2q$. \end{lemma}

\begin{proof}
By induction, using the property $\sum_{v\in V} L^{i+1}(v) \ge \sum_{v\in V} L^{i}(v)+2$ from Lemma \ref{sum}. For the induction base note that $\sum_{v\in V} L^{0}(v) = 0$ 
because $G^0$ does not contain any edges and thus no vertex has a strictly decreasing trail of length greater than 0. \qed \end{proof}

\noindent We next prove the lower bound on the length of longest strictly decreasing trails.

\begin{theorem}Let $G = (V,E)$ be an undirected edge-weighted graph such that $|V|=n$ and $|E| = q$. Let  
$w:E\rightarrow \{1,\ldots,q\}$ be a weight function assuming different weights are mapped to to different edges. 
Then, $P_d(w,G) \ge 2\cdot\lfloor\frac{q}{n}\rfloor$ i.e., there 
exists a strictly decreasing trail of length $2\cdot\lfloor\frac{q}{n}\rfloor$.\label{main}\end{theorem}

\begin{proof}Assume that no vertex is a starting point of a trail of length at least $2\cdot\lfloor\frac{q}{n}\rfloor$, that is
	$L^{q}(v) < 2\cdot\lfloor\frac{q}{n}\rfloor,$ for all $v \in V$. 
	Then, $\sum_{v\in V} L^{q}(v) < 2\cdot\lfloor\frac{q}{n}\rfloor n \le 2\cdot q$. But this is a contradiction 
	to Lemma 2 that postulates that the sum of the length of all longest strictly decreasing trails $\sum_{v\in V} L^{q}(v)$ is greater than $2\cdot q$.
	Hence, there has to be at least one vertex with a strictly decreasing trail that is longer than $2\cdot\lfloor\frac{q}{n}\rfloor$ in $G^q$.
	This trail contains a subtrail of length $2\cdot\lfloor\frac{q}{n}\rfloor$. Since $E^q=E$ it follows that $G^q=G$, which concludes 
	the proof. 
\end{proof} 

\noindent Based on Theorem \ref{main}, we get the following results.

\begin{corollary}\label{corInc}
It also holds that $P_i(w,G) \ge 2\cdot\lfloor\frac{q}{n}\rfloor$ since when reversing a strictly decreasing trail 
one obtains a strictly increasing one. In this case, define $L^i(v)$ as the 
length of a longest strictly increasing trail ending at $v$ in $G^i$.\qed \end{corollary}

\begin{corollary}
Let G be as in Theorem \ref{main} and additionally assume that G is complete. Then, there exists a trail 
of length at least $n-1$, i.e. $f_i(n) = f_d(n)  \ge n-1$.\qed
\end{corollary}

In \cite{graham1973increasing} the authors present a non-constructive proof. As in Lemma \ref{sum} they argue that the 
sum of the lengths of all increasing paths is at least 2. We however, use the exact increase therefore 
making the proof constructive and obtaining Algorithm \ref{algo}.\<close>

section "Formalization of Trail Properties in Isabelle/HOL"
text \<open>\label{Formalization} \<close>
subsection "Graph Theory in the Archive of Formal Proofs"

text \<open>\label{GraphTheory} To increase the reusability of our library we build upon the @{text "Graph_Theory"}
library by Noschinski \cite{Graph_Theory-AFP}. Graphs are represented as records consisting of vertices and edges that
can be accessed using the selectors @{term "pverts"} and @{term "parcs"}. We recall the definition 
of the type @{term pair_pre_digraph}:

 @{text [display = true] "record 'a pair_pre_digraph = pverts :: \"'a set\" parcs :: \"'a rel\""}

Now restrictions upon the two sets and new features can be introduced using locales. 
Locales are Isabelle's way to deal with parameterized theories~\cite{ballarin2010tutorial}. Consider
for example @{locale pair_wf_digraph}.
The endpoints of an edge can be accessed using the functions @{text fst} and @{text snd}. Therefore, conditions
@{text "arc_fst_in_verts"} and @{text "arc_snd_in_verts"} assert that both endpoints of an edge are
vertices. Using so-called sublocales a variety of other graphs are defined.  

@{text [display = true] "locale pair_wf_digraph = pair_pre_digraph +
  assumes arc_fst_in_verts: \"\<And>e. e \<in> parcs G \<Longrightarrow> fst e \<in> pverts G\"
  assumes arc_snd_in_verts: \"\<And>e. e \<in> parcs G \<Longrightarrow> snd e \<in> pverts G\""}

An object of type @{text "'b awalk"} is defined in @{text "Graph_Theory.Arc_Walk"} as a list of edges. 
Additionally, the definition @{text "awalk"} imposes that both endpoints of a walk are vertices of 
the graph, all elements of the walk are edges and two subsequent edges share a common vertex. \vspace{1em}

\noindent@{text "type_synonym 'b awalk = \"'b list\""}

@{text [display = true] "definition awalk :: \"'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool\"
\"awalk u p v \<equiv> u \<in> verts G \<and> set p \<subseteq> arcs G \<and> cas u p v\" "}

\noindent We also reuse the type synonym @{text "weight_fun"} introduced in \mbox{@{text "Weighted_Graph"}}. \vspace{1em}

@{text "type_synonym 'b weight_fun = \"'b \<Rightarrow> real\""}  \vspace{1em}

Finally, there is an useful definition capturing the notion of a complete graph, namely @{text "complete_digraph"}. \<close>

subsection "Increasing and Decreasing Trails in Weighted Graphs"

text \<open>\label{trails} In our work we extend the graph theory framework from Section \ref{GraphTheory} 
with new features enabling reasoning about ordered trails. To this end,
 a trail is defined as a list of edges. We will only consider strictly increasing trails 
on graphs without parallel edges. For this we require the graph 
to be of type @{term "pair_pre_digraph"}, as introduced in Section \ref{GraphTheory}. 

Two different definitions
are given in our formalization. Function @{text "incTrail"} can be used without specifying the first and last vertex of the trail
whereas @{text "incTrail2"} uses more of @{term "Graph_Theory's"} predefined features. Moreover, making use of  monotonicity
\mbox{@{text "incTrail"}} only requires to check if one edge's weight is smaller than its successors' while @{text "incTrail2"}
checks if the weight is smaller than the one of all subsequent edges in the sequence, i.e. if the list 
is sorted. The {\em equivalence
between the two notions} is shown in the following.\<close>

fun incTrail :: "'a pair_pre_digraph \<Rightarrow> ('a \<times>'a) weight_fun \<Rightarrow> ('a \<times>'a) list \<Rightarrow> bool" where
"incTrail g w [] = True" |
"incTrail g w [e\<^sub>1] = (e\<^sub>1 \<in> parcs g)" |
"incTrail g w (e\<^sub>1#e\<^sub>2#es) = (if w e\<^sub>1 < w e\<^sub>2 \<and> e\<^sub>1 \<in> parcs g \<and> snd e\<^sub>1 = fst e\<^sub>2 
                                    then incTrail g w (e\<^sub>2#es) else False)"

definition(in pair_pre_digraph) incTrail2 where
"incTrail2 w es u v \<equiv> sorted_wrt (\<lambda> e\<^sub>1 e\<^sub>2. w e\<^sub>1 < w e\<^sub>2) es \<and> (es = [] \<or> awalk u es v)"
(*definition(in pair_pre_digraph) incTrail2b where (* Use this instead? *)
"incTrail2b w es u v \<equiv> (\<forall> es\<^sub>1 e\<^sub>1 e\<^sub>2 es\<^sub>2. es = es\<^sub>1 @ [e\<^sub>1,e\<^sub>2] @ es\<^sub>2 \<longrightarrow> w e\<^sub>1 < w e\<^sub>2) \<and> (es = [] \<or> awalk u es v)"*)

fun decTrail :: "'a pair_pre_digraph \<Rightarrow> ('a \<times>'a) weight_fun \<Rightarrow> ('a \<times>'a) list \<Rightarrow> bool" where
"decTrail g w [] = True" |
"decTrail g w [e\<^sub>1] = (e\<^sub>1 \<in> parcs g)" |
"decTrail g w (e\<^sub>1#e\<^sub>2#es) = (if w e\<^sub>1 > w e\<^sub>2 \<and> e\<^sub>1 \<in> parcs g \<and> snd e\<^sub>1 = fst e\<^sub>2 
                                    then decTrail g w (e\<^sub>2#es) else False)"

definition(in pair_pre_digraph) decTrail2 where 
"decTrail2 w es u v \<equiv> sorted_wrt (\<lambda> e\<^sub>1 e\<^sub>2. w e\<^sub>1 > w e\<^sub>2) es \<and> (es = [] \<or> awalk u es v)"

text \<open> Defining trails as lists in Isabelle has many advantages including using predefined list operators, 
e.g., drop. Thus, we can show one result that will be constantly needed in the following, that is, that
{\em any subtrail of an ordered trail is an ordered trail itself}.\<close>

lemma incTrail_subtrail:
  assumes "incTrail g w es"
  shows "incTrail g w (drop k es)" 
(*<*)proof (induction k)
  show "incTrail g w (drop 0 es)" using assms by simp
next 
  fix k
  assume IH: "incTrail g w (drop k es)"
  show "incTrail g w (drop (Suc k) es)" 
  proof cases
    assume "length (drop (Suc k) es) = 0"
    then show ?thesis by simp
  next
    assume a0: "length (drop (Suc k) es) \<noteq> 0"
    then have "\<exists> e\<^sub>2. (drop (Suc k) es) = e\<^sub>2 # (drop (Suc (Suc k)) es)" 
      by (metis Cons_nth_drop_Suc drop_eq_Nil length_0_conv not_less)
    then have "\<exists> e\<^sub>1. \<exists> e\<^sub>2. (drop k es) = e\<^sub>1 # e\<^sub>2 # (drop (Suc (Suc k)) es)"
      by (metis Cons_nth_drop_Suc drop_Suc drop_eq_Nil linorder_not_less list.sel(2) tl_drop)
    then show ?thesis 
      by (metis IH drop_Suc incTrail.simps(3) list.sel(3) tl_drop)
  qed
qed(*>*)

text \<open> \<close>

lemma decTrail_subtrail: 
  assumes "decTrail g w es"
  shows "decTrail g w (drop k es)" 
(*<*)proof (induction k)
  show "decTrail g w (drop 0 es)" using assms by simp
next 
  fix k
  assume IH: "decTrail g w (drop k es)"
  show "decTrail g w (drop (Suc k) es)" 
  proof cases
    assume "length (drop (Suc k) es) = 0"
    then show ?thesis by simp
  next
    assume a0: "length (drop (Suc k) es) \<noteq> 0"
    then have "\<exists> e\<^sub>2. (drop (Suc k) es) = e\<^sub>2 # (drop (Suc (Suc k)) es)" 
      by (metis Cons_nth_drop_Suc drop_eq_Nil length_0_conv not_less)
    then have "\<exists> e\<^sub>1. \<exists> e\<^sub>2. (drop k es) = e\<^sub>1 # e\<^sub>2 # (drop (Suc (Suc k)) es)" 
      by (metis Cons_nth_drop_Suc drop_Suc drop_eq_Nil linorder_not_less list.sel(2) tl_drop)
    then show ?thesis 
      by (metis IH drop_Suc decTrail.simps(3) list.sel(3) tl_drop)
  qed
qed

lemma incTrail_subtrail_cons[simp]:
  assumes "incTrail g w (e#es)"
  shows "incTrail g w es" 
proof-
  have "drop 1 (e#es) = es" by simp
  then show ?thesis 
    by (metis assms incTrail_subtrail)
qed

lemma decTrail_subtrail_cons[simp]:
  assumes "decTrail g w (e#es)"
  shows "decTrail g w es" 
proof-
  have "drop 1 (e#es) = es" by simp
  then show ?thesis 
    by (metis assms decTrail_subtrail)
qed

lemma incTrail_append:
  assumes "incTrail G w es" and "length es \<ge> 1 \<longrightarrow> w (last es) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)" 
  and "(v\<^sub>1,v\<^sub>2) \<in> arcs G" 
  shows "incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
proof-
  have "\<forall> es v\<^sub>1 v\<^sub>2. length es = k \<longrightarrow> (incTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])" for k
  proof(induction k)
    show "\<forall> es v\<^sub>1 v\<^sub>2. length es = 0 \<longrightarrow> (incTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
      by auto
  next
    fix k
    assume IH: "\<forall> es v\<^sub>1 v\<^sub>2. length es = k \<longrightarrow> (incTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
    show "\<forall> es v\<^sub>1 v\<^sub>2. length es = (Suc k) \<longrightarrow> (incTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
    proof(intro allI, intro impI)
      fix es :: "('a\<times>'a) list" and v\<^sub>1 v\<^sub>2 :: "'a"
      assume a0: "length es = (Suc k)" and a1: "(incTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G)"
      show "incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
      proof cases
        assume a2: "length (tl es) = 0"
        then have "hd es \<in> parcs G" 
          using a0 a1 
          by (metis hd_Cons_tl incTrail.simps(2) length_0_conv nat.simps(3))
        moreover have "w (hd es) < w (v\<^sub>1,v\<^sub>2)" 
          using a0 a1 a2 
          by (metis One_nat_def Suc_le_lessD hd_Cons_tl last_ConsL le_add1 length_0_conv length_greater_0_conv plus_1_eq_Suc)
        moreover have "snd (hd es) = v\<^sub>1" 
          using a0 a1 a2 
          by (metis hd_Cons_tl last_ConsL le_add1 length_0_conv nat.simps(3) plus_1_eq_Suc)
        moreover have "(incTrail G w (tl es) \<and> (length (tl es) \<ge> 1 \<longrightarrow> w (last (tl es)) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es))) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> incTrail G w ((tl es)@[(v\<^sub>1,v\<^sub>2)])"
          using IH a0 by auto
        ultimately show "incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])" 
          using a0 a1 a2 
          by (metis (no_types, hide_lams) append_Cons append_Nil fst_conv hd_Cons_tl incTrail.simps(1,3) 
              le_numeral_extra(2) length_0_conv list.size(3) nat.simps(3))
      next
        assume a2: "length (tl es) \<noteq> 0"
        moreover have f1: "w (last (tl es)) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G" 
          using a0 a1 a2
          by (metis last_tl le_add1 list.size(3) plus_1_eq_Suc)
        moreover have "w (hd (es@[(v\<^sub>1,v\<^sub>2)])) < w (hd (tl (es@[(v\<^sub>1,v\<^sub>2)])))"
          using a1 a2
          by (metis hd_Cons_tl hd_append2 incTrail.simps(3) list.sel(2) list.size(3) tl_append2)
        moreover have "(hd (es@[(v\<^sub>1,v\<^sub>2)])) \<in> parcs G" 
          using a1 a2 
          by (metis hd_Cons_tl hd_append2 incTrail.simps(3) list.size(3) neq_Nil_conv tl_Nil)
        moreover have "snd (hd (es@[(v\<^sub>1,v\<^sub>2)])) = fst (hd (tl (es@[(v\<^sub>1,v\<^sub>2)])))"
          using a0 a1 a2 
          by (metis One_nat_def hd_append2 incTrail.simps(3) length_tl list.collapse list.size(3) nat.simps(3) tl_append2)
        moreover have "(es@[(v\<^sub>1,v\<^sub>2)]) = (hd (es@[(v\<^sub>1,v\<^sub>2)])) # hd(tl (es@[(v\<^sub>1,v\<^sub>2)])) # tl (tl (es@[(v\<^sub>1,v\<^sub>2)]))" 
          using a0 a2
          by (metis append_is_Nil_conv hd_Cons_tl le_add1 le_numeral_extra(2) list.size(3) plus_1_eq_Suc tl_append2) 
        moreover have "(incTrail G w (tl es) \<and> (length (tl es) \<ge> 1 \<longrightarrow> w (last (tl es)) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es))) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> incTrail G w ((tl es)@[(v\<^sub>1,v\<^sub>2)])"
          using IH a0 by auto
        moreover have "(length (tl es) \<ge> 1 \<longrightarrow> w (last (tl es)) < w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es)))" 
          using f1 by blast
        moreover have "incTrail G w (tl es)"
        proof-
          have "drop 1 es = tl es" by (simp add: drop_Suc)
          then show ?thesis using a1 incTrail_subtrail by metis
        qed
        ultimately show "incTrail G w (es@[(v\<^sub>1,v\<^sub>2)])" 
          using a0 incTrail.simps(3)[of G w "(hd (es@[(v\<^sub>1,v\<^sub>2)]))" "(hd (tl (es@[(v\<^sub>1,v\<^sub>2)])))"]
          by (metis le_add1 le_numeral_extra(2) list.sel(3) list.size(3) plus_1_eq_Suc tl_append2)
      qed
    qed
  qed 
  then show ?thesis using assms by auto
qed

lemma decTrail_append: 
  assumes "decTrail G w xs" and "length xs \<ge> 1 \<longrightarrow> w (last xs) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last xs)" 
  and "(v\<^sub>1,v\<^sub>2) \<in> parcs G" 
  shows "decTrail G w (xs@[(v\<^sub>1,v\<^sub>2)])"
proof-
  have "\<forall> es v\<^sub>1 v\<^sub>2. length es = k \<longrightarrow> (decTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> decTrail G w (es@[(v\<^sub>1,v\<^sub>2)])" for k
  proof(induction k)
    show "\<forall> es v\<^sub>1 v\<^sub>2. length es = 0 \<longrightarrow> (decTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> decTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
      by auto
  next
    fix k
    assume IH: "\<forall> es v\<^sub>1 v\<^sub>2. length es = k \<longrightarrow> (decTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> decTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
    show "\<forall> es v\<^sub>1 v\<^sub>2. length es = (Suc k) \<longrightarrow> (decTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> decTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
    proof(intro allI, intro impI)
      fix es :: "('a\<times>'a) list" and v\<^sub>1 v\<^sub>2 :: "'a"
      assume a0: "length es = (Suc k)" and a1: "(decTrail G w es \<and> (length es \<ge> 1 \<longrightarrow> w (last es) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G)"
      show "decTrail G w (es@[(v\<^sub>1,v\<^sub>2)])"
      proof cases
        assume a2: "length (tl es) = 0"
        then have "hd es \<in> parcs G" 
          using a0 a1 
          by (metis hd_Cons_tl decTrail.simps(2) length_0_conv nat.simps(3))
        moreover have "w (hd es) > w (v\<^sub>1,v\<^sub>2)" 
          using a0 a1 a2 
          by (metis One_nat_def Suc_le_lessD hd_Cons_tl last_ConsL le_add1 length_0_conv length_greater_0_conv plus_1_eq_Suc)
        moreover have "snd (hd es) = v\<^sub>1" 
          using a0 a1 a2 
          by (metis hd_Cons_tl last_ConsL le_add1 length_0_conv nat.simps(3) plus_1_eq_Suc)
        moreover have "(decTrail G w (tl es) \<and> (length (tl es) \<ge> 1 \<longrightarrow> w (last (tl es)) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es))) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> decTrail G w ((tl es)@[(v\<^sub>1,v\<^sub>2)])"
          using IH a0 by auto
        ultimately show "decTrail G w (es@[(v\<^sub>1,v\<^sub>2)])" 
          using a0 a1 a2 
          by (metis (no_types, hide_lams) append_Cons append_Nil fst_conv hd_Cons_tl decTrail.simps(1,3) 
              le_numeral_extra(2) length_0_conv list.size(3) nat.simps(3))
      next
        assume a2: "length (tl es) \<noteq> 0"
        moreover have f1: "w (last (tl es)) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es)) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G" 
          using a0 a1 a2
          by (metis last_tl le_add1 list.size(3) plus_1_eq_Suc)
        moreover have "w (hd (es@[(v\<^sub>1,v\<^sub>2)])) > w (hd (tl (es@[(v\<^sub>1,v\<^sub>2)])))"
          using a1 a2
          by (metis hd_Cons_tl hd_append2 decTrail.simps(3) list.sel(2) list.size(3) tl_append2)
        moreover have "(hd (es@[(v\<^sub>1,v\<^sub>2)])) \<in> parcs G" 
          using a1 a2 
          by (metis hd_Cons_tl hd_append2 decTrail.simps(3) list.size(3) neq_Nil_conv tl_Nil)
        moreover have "snd (hd (es@[(v\<^sub>1,v\<^sub>2)])) = fst (hd (tl (es@[(v\<^sub>1,v\<^sub>2)])))"
          using a0 a1 a2 
          by (metis One_nat_def hd_append2 decTrail.simps(3) length_tl list.collapse list.size(3) nat.simps(3) tl_append2)
        moreover have "(es@[(v\<^sub>1,v\<^sub>2)]) = (hd (es@[(v\<^sub>1,v\<^sub>2)])) # hd(tl (es@[(v\<^sub>1,v\<^sub>2)])) # tl (tl (es@[(v\<^sub>1,v\<^sub>2)]))" 
          using a0 a2
          by (metis append_is_Nil_conv hd_Cons_tl le_add1 le_numeral_extra(2) list.size(3) plus_1_eq_Suc tl_append2) 
        moreover have "(decTrail G w (tl es) \<and> (length (tl es) \<ge> 1 \<longrightarrow> w (last (tl es)) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es))) \<and> (v\<^sub>1,v\<^sub>2) \<in> parcs G) \<longrightarrow> decTrail G w ((tl es)@[(v\<^sub>1,v\<^sub>2)])"
          using IH a0 by auto
        moreover have "(length (tl es) \<ge> 1 \<longrightarrow> w (last (tl es)) > w (v\<^sub>1,v\<^sub>2) \<and> v\<^sub>1 = snd (last (tl es)))" 
          using f1 by blast
        moreover have "decTrail G w (tl es)"
        proof-
          have "drop 1 es = tl es" by (simp add: drop_Suc)
          then show ?thesis using a1 decTrail_subtrail by metis
        qed
        ultimately show "decTrail G w (es@[(v\<^sub>1,v\<^sub>2)])" 
          using a0 decTrail.simps(3)[of G w "(hd (es@[(v\<^sub>1,v\<^sub>2)]))" "(hd (tl (es@[(v\<^sub>1,v\<^sub>2)])))"]
          by (metis le_add1 le_numeral_extra(2) list.sel(3) list.size(3) plus_1_eq_Suc tl_append2)
      qed
    qed
  qed 
  then show ?thesis using assms by auto
qed

lemma aux_incTrail_distinct:
  shows "incTrail g w es \<longrightarrow> (\<forall> e \<in> set (tl es) . w (hd es) < w e)" 
proof(induction es)
  show "incTrail g w [] \<longrightarrow> (\<forall> e \<in> set (tl []) . w (hd []) < w e)" by simp
next
  fix e\<^sub>1 es
  assume IH: "incTrail g w es \<longrightarrow> (\<forall> e \<in> set (tl es) . w (hd es) < w e)" 
  show "incTrail g w (e\<^sub>1#es) \<longrightarrow> (\<forall> e \<in> set (tl (e\<^sub>1#es)) . w (hd (e\<^sub>1#es)) < w e)" 
  proof
    assume a0: "incTrail g w (e\<^sub>1#es)"
    then have "\<forall> e \<in> set (tl es) . w (hd es) < w e" using IH by simp
    moreover have "es \<noteq> [] \<longrightarrow> w e\<^sub>1 < w (hd es)" 
      using a0 incTrail.elims(2) by fastforce
    ultimately have "\<forall> e \<in> set es . w e\<^sub>1 < w e"
      by (smt empty_iff hd_Cons_tl list.set(1) set_ConsD)
    then show "\<forall> e \<in> set (tl (e\<^sub>1#es)) . w (hd (e\<^sub>1#es)) < w e" by simp
  qed
qed

lemma aux_decTrail_distinct:
  shows "decTrail g w es \<longrightarrow> (\<forall> e \<in> set (tl es) . w (hd es) > w e)" 
proof(induction es)
  show "decTrail g w [] \<longrightarrow> (\<forall> e \<in> set (tl []) . w (hd []) > w e)" by simp
next
  fix e\<^sub>1 es
  assume IH: "decTrail g w es \<longrightarrow> (\<forall> e \<in> set (tl es) . w (hd es) > w e)" 
  show "decTrail g w (e\<^sub>1#es) \<longrightarrow> (\<forall> e \<in> set (tl (e\<^sub>1#es)) . w (hd (e\<^sub>1#es)) > w e)" 
  proof
    assume a0: "decTrail g w (e\<^sub>1#es)"   
    then have "(\<forall> e \<in> set (tl es) . w (hd es) > w e)" using IH by simp
    moreover have "es \<noteq> [] \<longrightarrow> w e\<^sub>1 > w (hd es)" 
      using a0 decTrail.elims(2) by fastforce
    ultimately have "\<forall> e \<in> set es . w e\<^sub>1 > w e" 
      by (smt empty_iff hd_Cons_tl list.set(1) set_ConsD)
    then show "\<forall> e \<in> set (tl (e\<^sub>1#es)) . w (hd (e\<^sub>1#es)) > w e" by simp
  qed
qed

lemma(in pair_wf_digraph) incTrail_is_walk:
  assumes "k \<ge> 1"
  shows "\<forall> es. length es = k \<longrightarrow> incTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k \<ge> 1" using assms by simp
next
  show "\<forall> es. length es = 1 \<longrightarrow> incTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))"
  proof safe
    fix es
    assume a0: "length es = 1" and a1: "incTrail G w es"
    then obtain e where f0: "es = [e]" 
      by (metis One_nat_def Suc_le_length_iff add_diff_cancel_left' le_numeral_extra(4) length_0_conv length_tl list.sel(3) plus_1_eq_Suc)
    then have "awalk (fst e) es (snd e)" 
      using a1 arc_implies_awalk by auto 
    then show "(trail (fst (hd es)) es (snd (last es)))" 
      using f0 trail_Cons_iff trail_Nil_iff by auto
  qed
next
  fix k :: nat
  assume a0: "k \<ge> 1" 
  assume IH: "\<forall> es. length es = k \<longrightarrow> incTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
  show "\<forall> es. length es = Suc k \<longrightarrow> incTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
  proof safe
    fix es 
    assume a1: "length es = Suc k" and a2: "incTrail G w es" 
    then obtain e ess where f0: "es = e # ess" by (meson length_Suc_conv)
    have f1: "e \<in> parcs G" using a2 f0 incTrail.elims(2) by fastforce 
    have f2: "awalk (fst (hd ess)) ess (snd (last ess)) \<and> distinct ess"
    proof-
      have "length ess = k" using a1 f0 by auto
      moreover have "incTrail G w ess" 
        by (metis a2 drop0 drop_Suc_Cons f0 incTrail_subtrail)
      ultimately have "(trail (fst (hd ess)) ess (snd (last ess)))" 
        using IH by auto
      then show ?thesis 
        by (simp add: trail_def)
    qed
    have "awalk (fst (hd (e#ess))) (e#ess) (snd (last (e#ess)))" 
    proof-
      have "(fst (hd (e#ess))) \<in> verts G" using f1 by simp
      moreover have "set (e#ess) \<subseteq> arcs G" using f1 f2 by auto
      moreover have "cas (fst e) (e#ess) (snd (last ess))" 
      proof-
        have "length ess = k" 
          using a1 f0 by auto
        then have "(fst (hd ess)) = snd e" 
          by (metis a0 a2 f0 incTrail.simps(3) le_numeral_extra(2) list.exhaust_sel list.size(3))
        then have "cas (snd e) ess (snd (last ess))" using f2 
          by (simp add: awalk_def)
        moreover have "tail G e = (fst e)" by simp
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis 
        by (simp add: awalk_def)
    qed
    moreover have "distinct (e # ess)" 
    proof-
      have "(\<forall> y \<in> set (tl es) . w (hd es) < w y)" using a1 aux_incTrail_distinct a2 by blast
      then show ?thesis 
        using f2 f0 by auto
    qed
    ultimately show "(trail (fst (hd es)) es (snd (last es)))"
      using f0 trail_def by simp
  qed
qed

lemma(in pair_wf_digraph) decTrail_is_walk:
  assumes "k \<ge> 1"
  shows "\<forall> es. length es = k \<longrightarrow> decTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k \<ge> 1" using assms by simp
next
  show "\<forall> es. length es = 1 \<longrightarrow> decTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))"
  proof safe
    fix es
    assume a0: "length es = 1" and a1: "decTrail G w es"
    then obtain e where f0: "es = [e]" 
      by (metis One_nat_def Suc_le_length_iff add_diff_cancel_left' le_numeral_extra(4) length_0_conv length_tl list.sel(3) plus_1_eq_Suc)
    then have "awalk (fst e) es (snd e)" 
      using a1 arc_implies_awalk by auto 
    then show "(trail (fst (hd es)) es (snd (last es)))" 
      using f0 trail_Cons_iff trail_Nil_iff by auto
  qed
next
  fix k :: nat
  assume a0: "k \<ge> 1" 
  assume IH: "\<forall> es. length es = k \<longrightarrow> decTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
  show "\<forall> es. length es = Suc k \<longrightarrow> decTrail G w es \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
  proof safe
    fix es 
    assume a1: "length es = Suc k" and a2: "decTrail G w es" 
    then obtain e ess where f0: "es = e # ess" by (meson length_Suc_conv)
    have f1: "e \<in> parcs G" using a2 f0 decTrail.elims(2) by fastforce 
    have f2: "awalk (fst (hd ess)) ess (snd (last ess)) \<and> distinct ess"
    proof-
      have "length ess = k" using a1 f0 by auto
      moreover have "decTrail G w ess" 
        by (metis a2 drop0 drop_Suc_Cons f0 decTrail_subtrail)
      ultimately have "(trail (fst (hd ess)) ess (snd (last ess)))" 
        using IH by auto
      then show ?thesis 
        by (simp add: trail_def)
    qed
    have "awalk (fst (hd (e#ess))) (e#ess) (snd (last (e#ess)))" 
    proof-
      have "(fst (hd (e#ess))) \<in> verts G" using f1 by simp
      moreover have "set (e#ess) \<subseteq> arcs G" using f1 f2 by auto
      moreover have "cas (fst e) (e#ess) (snd (last ess))" 
      proof-
        have "length ess = k" 
          using a1 f0 by auto
        then have "(fst (hd ess)) = snd e" 
          by (metis a0 a2 f0 decTrail.simps(3) le_numeral_extra(2) list.exhaust_sel list.size(3))
        then have "cas (snd e) ess (snd (last ess))" using f2 
          by (simp add: awalk_def)
        moreover have "tail G e = (fst e)" by simp
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis 
        by (simp add: awalk_def)
    qed
    moreover have "distinct (e # ess)" 
    proof-
      have "(\<forall> y \<in> set (tl es) . w (hd es) > w y)" using a1 aux_decTrail_distinct a2 by blast
      then show ?thesis 
        using f2 f0 by auto
    qed
    ultimately show "(trail (fst (hd es)) es (snd (last es)))"
      using f0 trail_def by simp
  qed
qed

lemma(in pair_wf_digraph) incTrail2_is_incTrail:
  shows "incTrail2 w es (fst (hd es)) (snd (last es)) \<longrightarrow> incTrail G w es" 
proof(induction es)
  show "incTrail2 w [] (fst (hd [])) (snd (last [])) \<longrightarrow> incTrail G w []" by auto
next
  fix e es 
  assume IH: "incTrail2 w es (fst (hd es)) (snd (last es)) \<longrightarrow> incTrail G w es" 
  show "incTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es))) \<longrightarrow> incTrail G w (e#es)" 
  proof(rule disjE)
    show "(\<exists>y ys. es = y # ys) \<or> es = []" 
      using list.exhaust by blast 
  next
    assume "es = []" 
    then have "incTrail2 w [e] (fst e) (snd e) \<longrightarrow> e \<in> parcs G" 
      by (simp add: awalk_Cons_iff incTrail2_def)                                       
    then have "incTrail2 w [e] (fst e) (snd e) \<longrightarrow> decTrail G w [e]"
      using decTrail.simps(2) by blast
    then show "incTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es))) \<longrightarrow> incTrail G w (e#es)" 
      by (simp add: \<open>es = []\<close>)
  next
    assume "\<exists>y ys. es = y # ys"
    then obtain y ys where f0: "es = y # ys" by blast
    show "incTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es))) \<longrightarrow> incTrail G w (e#es)" 
    proof
      assume a0: "incTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es)))"
      then have f1: "incTrail2 w (e#es) (fst e) (snd (last es))" by (simp add: f0)
      have "incTrail2 w (es) (fst (hd (es))) (snd (last (es)))" 
        using a0 
        by (simp add: awalk_Cons_iff incTrail2_def f0)
      then have "incTrail G w es" using IH by auto
      moreover have "w e < w y" using f0 f1  
        by (simp add: incTrail2_def pair_wf_digraph_axioms)
      moreover have "e \<in> parcs G" using f1 
        by (simp add: awalk_Cons_iff incTrail2_def)
      moreover have "snd e = fst y" using f0 f1 decTrail2_def 
        by (simp add: incTrail2_def awalk_Cons_iff)
      ultimately show "incTrail G w (e#es)" 
        by (simp add: f0)
    qed
  qed
qed

lemma(in pair_wf_digraph) decTrail2_is_decTrail:
  shows "decTrail2 w es (fst (hd es)) (snd (last es)) \<longrightarrow> decTrail G w es" 
proof(induction es)
  show "decTrail2 w [] (fst (hd [])) (snd (last [])) \<longrightarrow> decTrail G w []" by auto
next
  fix e es
  assume IH: "decTrail2 w es (fst (hd es)) (snd (last es)) \<longrightarrow> decTrail G w es" 
  show "decTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es))) \<longrightarrow> decTrail G w (e#es)" 
  proof(rule disjE)
    show "(\<exists>y ys. es = y # ys) \<or> es = []" 
      using list.exhaust by blast 
  next
    assume "es = []" 
    then have "decTrail2 w [e] (fst e) (snd e) \<longrightarrow> e \<in> parcs G" 
      by (simp add: awalk_Cons_iff decTrail2_def)
    then have "decTrail2 w [e] (fst e) (snd e) \<longrightarrow> decTrail G w [e]"
      using decTrail.simps(2) by blast
    then show "decTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es))) \<longrightarrow> decTrail G w (e#es)" 
      by (simp add: \<open>es = []\<close>)
  next
    assume "\<exists>y ys. es = y # ys"
    then obtain y ys where f0: "es = y # ys" by blast
    show "decTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es))) \<longrightarrow> decTrail G w (e#es)" 
    proof
      assume a0: "decTrail2 w (e#es) (fst (hd (e#es))) (snd (last (e#es)))"
      then have f1: "decTrail2 w (e#es) (fst e) (snd (last es))" by (simp add: f0)
      have "decTrail2 w es (fst (hd (es))) (snd (last (es)))" 
        using a0 
        by (simp add: awalk_Cons_iff decTrail2_def f0)
      then have "decTrail G w es" using IH by auto
      moreover have "w e > w y" using f0 f1 decTrail2_def 
        by (simp add: decTrail2_def pair_wf_digraph_axioms)
      moreover have "e \<in> parcs G" using f1 
        by (simp add: awalk_Cons_iff decTrail2_def)
      moreover have "snd e = fst y" using f0 f1 decTrail2_def 
        by (simp add: decTrail2_def awalk_Cons_iff)
      ultimately show "decTrail G w (e#es)" 
        by (simp add: f0)
    qed
  qed
qed(*>*)

text \<open> In Isabelle we then show the equivalence between the two definitions @{term "decTrail"} and @{term "decTrail2"} of strictly decreasing trails.
Similarly, we also show the equivalence between the definition @{term "incTrail"} and @{term "incTrail2"} of strictly increasing trails.\<close>

lemma(in pair_wf_digraph) decTrail_is_dec_walk:
  shows "decTrail G w es \<longleftrightarrow> decTrail2 w es (fst (hd es)) (snd (last es))" 
(*<*)proof
  assume a0: "decTrail G w es" 
  moreover have "decTrail G w es \<longrightarrow> sorted_wrt (\<lambda> x y. w x > w y) es" 
  proof(induction es) 
    show "decTrail G w [] \<longrightarrow> sorted_wrt (\<lambda> x y. w x > w y) []" by auto
  next
    fix x xs
    assume IH: "decTrail G w xs \<longrightarrow> sorted_wrt (\<lambda> x y. w x > w y) xs" 
    show "decTrail G w (x#xs) \<longrightarrow> sorted_wrt (\<lambda> x y. w x > w y) (x#xs)" 
    proof(rule disjE)
      show "length xs \<ge> 1 \<or> length xs = 0" by linarith
    next
      assume a0: "length xs \<ge> 1"
      show "decTrail G w (x#xs) \<longrightarrow> sorted_wrt (\<lambda> x y. w x > w y) (x#xs)" 
      proof
        assume a1: "decTrail G w (x#xs)"
        then have "decTrail G w xs" 
          by (metis drop0 drop_Suc_Cons decTrail_subtrail)
        then have "sorted_wrt (\<lambda> x y. w x > w y) xs" using IH by auto
        moreover have "w x > w (hd xs) \<and> x \<in> parcs G \<and> snd x = fst (hd xs)" using IH a0 
          by (metis a1 hd_Cons_tl decTrail.simps(3) leD less_numeral_extra(1) list.size(3))
        ultimately show "sorted_wrt (\<lambda> x y. w x > w y) (x#xs)" 
          by (smt a0 hd_Cons_tl length_greater_0_conv less_le_trans rel_simps(68) set_ConsD sorted_wrt.simps(2))
      qed
    next
      assume "length xs = 0" 
      then show "decTrail G w (x#xs) \<longrightarrow> sorted_wrt (\<lambda> x y. w x > w y) (x#xs)" by auto
    qed
  qed
  moreover have "(es = [] \<or> awalk (fst (hd es)) es (snd (last es)))"
  proof-
    have "es \<noteq> [] \<longrightarrow> length es \<ge> 1" 
      by (simp add: Suc_le_eq)
    then have "es \<noteq> [] \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
      using decTrail_is_walk 
      using a0 by blast
    then show ?thesis 
      using trail_def by blast
  qed
  ultimately show "decTrail2 w es (fst (hd es)) (snd (last es))" 
    by (simp add: decTrail2_def)
next
  assume "decTrail2 w es (fst (hd es)) (snd (last es))"
  then show "decTrail G w es" using decTrail2_is_decTrail by auto
qed(*>*)

text \<open> \<close>

lemma(in pair_wf_digraph) incTrail_is_inc_walk:
  shows "incTrail G w es \<longleftrightarrow> incTrail2 w es (fst (hd es)) (snd (last es))" 
(*<*)proof
  assume a0: "incTrail G w es" 
  moreover have "incTrail G w es \<longrightarrow> sorted_wrt (\<lambda> x y. w x < w y) es" 
  proof(induction es) 
    show "incTrail G w [] \<longrightarrow> sorted_wrt (\<lambda> x y. w x < w y) []" by auto
  next
    fix x xs
    assume IH: "incTrail G w xs \<longrightarrow> sorted_wrt (\<lambda> x y. w x < w y) xs" 
    show "incTrail G w (x#xs) \<longrightarrow> sorted_wrt (\<lambda> x y. w x < w y) (x#xs)" 
    proof(rule disjE)
      show "length xs \<ge> 1 \<or> length xs = 0" by linarith
    next
      assume a0: "length xs \<ge> 1"
      show "incTrail G w (x#xs) \<longrightarrow> sorted_wrt (\<lambda> x y. w x < w y) (x#xs)" 
      proof
        assume a1: "incTrail G w (x#xs)"
        then have "incTrail G w xs" 
          by (metis drop0 drop_Suc_Cons incTrail_subtrail)
        then have "sorted_wrt (\<lambda> x y. w x < w y) xs" using IH by auto
        moreover have "w x < w (hd xs) \<and> x \<in> parcs G \<and> snd x = fst (hd xs)" using IH a0 
          by (metis a1 hd_Cons_tl incTrail.simps(3) leD less_numeral_extra(1) list.size(3))
        ultimately show "sorted_wrt (\<lambda> x y. w x < w y) (x#xs)" 
          by (smt a0 hd_Cons_tl length_greater_0_conv less_le_trans rel_simps(68) set_ConsD sorted_wrt.simps(2))
      qed
    next
      assume "length xs = 0" 
      then show "incTrail G w (x#xs) \<longrightarrow> sorted_wrt (\<lambda> x y. w x < w y) (x#xs)" by auto
    qed
  qed
  moreover have "(es = [] \<or> awalk (fst (hd es)) es (snd (last es)))"
  proof-
    have "es \<noteq> [] \<longrightarrow> length es \<ge> 1" 
      by (simp add: Suc_le_eq)
    then have "es \<noteq> [] \<longrightarrow> (trail (fst (hd es)) es (snd (last es)))" 
      using incTrail_is_walk a0 by blast
    then show ?thesis 
      using trail_def by blast
  qed
  ultimately show "incTrail2 w es (fst (hd es)) (snd (last es))" 
    by (simp add: incTrail2_def)
next
  assume "incTrail2 w es (fst (hd es)) (snd (last es))"
  then show "incTrail G w es" using incTrail2_is_incTrail by auto
qed

lemma(in pair_sym_digraph) decTrail_implies_rev_incTrail:
  assumes "\<forall> v\<^sub>1 v\<^sub>2. w (v\<^sub>1,v\<^sub>2) = w(v\<^sub>2,v\<^sub>1)" 
  shows "decTrail G w es \<longrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es))"
proof(induction es)
  show "decTrail G w [] \<longrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) []))" by auto
next
  fix e\<^sub>1 es
  assume IH: "decTrail G w es \<longrightarrow> incTrail G w (rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) es))"
  show "decTrail G w (e\<^sub>1#es) \<longrightarrow> incTrail G w (rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) (e\<^sub>1#es)))"
  proof
    assume a0: "decTrail G w (e\<^sub>1#es)"
    show "incTrail G w (rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) (e\<^sub>1#es)))"
    proof(rule disjE)
      show "length es = 0 \<or> length es \<ge> 1" 
        using not_less by auto
    next
      assume "length es = 0"
      then show "incTrail G w (rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) (e\<^sub>1#es)))"
        using a0 arcs_symmetric
        by (metis (mono_tags, lifting) decTrail.simps(2) in_arcs_imp_in_arcs_ends incTrail.simps(2) length_0_conv list.map_disc_iff list.simps(9) prod.case_eq_if singleton_rev_conv)
    next
      assume a1: "length es \<ge> 1"
      then obtain e\<^sub>2 ess where "es = e\<^sub>2 # ess" 
        by (metis One_nat_def Suc_le_length_iff) 
      then have f1: "w e\<^sub>1 > w e\<^sub>2 \<and> e\<^sub>1 \<in> parcs G \<and> snd e\<^sub>1 = fst e\<^sub>2 \<and> decTrail G w (e\<^sub>2#ess)" 
        by (metis a0 decTrail.simps(3))
      then have "incTrail G w (rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) es))" using IH by (simp add: \<open>es = e\<^sub>2 # ess\<close>)
      moreover have "1 \<le> length (rev (map (\<lambda>(x\<^sub>1, x\<^sub>2). (x\<^sub>2, x\<^sub>1)) es))" 
        using a1 by auto
      moreover have "w (last (rev (map (\<lambda>(x\<^sub>1, x\<^sub>2). (x\<^sub>2, x\<^sub>1)) es))) < w (snd e\<^sub>1, fst e\<^sub>1)" 
      proof-
        have "(last (rev (map (\<lambda>(x\<^sub>1, x\<^sub>2). (x\<^sub>2, x\<^sub>1)) es))) = (snd e\<^sub>2, fst e\<^sub>2)" 
          by (simp add: \<open>es = e\<^sub>2 # ess\<close> case_prod_beta')
        moreover have "w e\<^sub>2 = w (snd e\<^sub>2, fst e\<^sub>2)" using arcs_symmetric assms by simp
        ultimately show ?thesis using f1 by (metis assms prod.collapse)
      qed
      moreover have "snd e\<^sub>1 = snd (last (rev (map (\<lambda>(x\<^sub>1, x\<^sub>2). (x\<^sub>2, x\<^sub>1)) es)))"           
        by (simp add: \<open>es = e\<^sub>2 # ess\<close> f1 case_prod_beta')
      moreover have "(snd e\<^sub>1, fst e\<^sub>1) \<in> parcs G" 
        using arcs_symmetric f1 in_arcs_imp_in_arcs_ends by blast
      ultimately have "incTrail G w (rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) es) @ [(snd e\<^sub>1, fst e\<^sub>1)])" 
        using IH incTrail_append[of G w "(rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) es))" "snd e\<^sub>1" "fst e\<^sub>1"] by auto
      moreover have "[(snd e\<^sub>1, fst e\<^sub>1)] = map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) [(fst e\<^sub>1, snd e\<^sub>1)]" 
        by (metis case_prod_conv list.simps(8) list.simps(9))
      moreover have "[(fst e\<^sub>1, snd e\<^sub>1)] = [e\<^sub>1]" by simp
      moreover have "rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) es) @ (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) [e\<^sub>1])
                   = rev ((map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) (e\<^sub>1#es)))"
        by simp
      ultimately show "incTrail G w (rev (map (\<lambda>(x\<^sub>1,x\<^sub>2). (x\<^sub>2,x\<^sub>1)) (e\<^sub>1#es)))" 
        by auto
    qed
  qed
qed

lemma(in pair_sym_digraph) incTrail_implies_rev_decTrail:
  assumes "\<forall> v\<^sub>1 v\<^sub>2. w (v\<^sub>1,v\<^sub>2) = w(v\<^sub>2,v\<^sub>1)" 
  shows "\<forall>es. length es = k \<longrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es)) \<longrightarrow> decTrail G w es"
proof(induction k)
  show "\<forall>es. length es = 0 \<longrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es)) \<longrightarrow> decTrail G w es" by auto
next
  fix k
  assume IH: "\<forall>es. length es = k \<longrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es)) \<longrightarrow> decTrail G w es"
  show "\<forall>es. length es = Suc k \<longrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es)) \<longrightarrow> decTrail G w es"
  proof(rule allI, rule impI, rule impI)
    fix es
    assume a0: "length es = Suc k" and a1: "incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es))"
    obtain e ess where f0: "es = ess @ [e]" 
      by (metis a0 append_Nil2 append_eq_conv_conj lessI take_hd_drop)
    then have "incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) (ess@[e])))" using a1 by auto
    then have f1: "incTrail G w ((snd e,fst e) # rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) ess))" 
      by (simp add: prod.case_eq_if) 
    moreover have "drop 1 ((snd e,fst e) # rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) ess)) = rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) ess)" by simp 
    ultimately have "incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) ess))" using incTrail_subtrail by metis
    moreover have "length (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) ess)) = k" 
      using a0 f0 by auto 
    ultimately have "decTrail G w ess" using IH by auto
    show "decTrail G w es"
    proof(rule disjE)
      show "length ess = 0 \<or> length ess \<ge> 1" by linarith
    next
      assume "length ess = 0" 
      then show "decTrail G w es" 
        using arcs_symmetric f0 f1 by force
    next
      assume a2: "length ess \<ge> 1" 
      then obtain z zs where f2: "ess = zs @ [z]" 
        by (metis le_numeral_extra(2) length_0_conv rev_exhaust)
      moreover have "rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) ess) = rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) (zs@[z]))" using f2 by auto
      moreover have "rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) (zs@[z])) = (snd z, fst z) # rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) zs)" by (simp add: prod.case_eq_if) 
      ultimately have "incTrail G w ((snd e,fst e) # (snd z, fst z) # rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) zs))" 
        using f1 by auto
      then have t3: "w (snd e,fst e) < w (snd z, fst z) \<and> (snd e,fst e) \<in> parcs G \<and> snd (snd e,fst e) = fst (snd z, fst z)"
        using f1 a2 f2 by (meson incTrail.simps(3))
      moreover have "(hd (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) ess))) = (snd z,fst z)" 
        by (simp add: f2 case_prod_beta')
      moreover have "w (fst e, snd e) < w (last ess)" 
        by (metis assms f2 last_snoc prod.collapse t3)
      moreover have "last ess = z" 
        by (simp add: f2)
      moreover have "fst e = snd (last ess)" 
        using calculation(4) t3 by auto 
      moreover have "(fst e, snd e) \<in> parcs G" 
        using arcs_symmetric t3 by blast
      ultimately have "decTrail G w (ess@[(fst e,snd e)])" 
        using decTrail_append[of G w ess "fst e" "snd e" ] 
        using \<open>decTrail G w ess\<close> by blast
      then show "decTrail G w es" 
        by (simp add: f0)
    qed
  qed
qed(*>*)


text \<open> Any strictly decreasing trail $(e_1,\ldots,e_n)$ can also be seen as a strictly increasing trail $(e_n,...,e_1)$
if the graph considered is undirected. To this end, we make use of the locale @{term "pair_sym_digraph"}
that captures the idea of symmetric arcs. However, it is also necessary to assume that the weight 
function assigns the same weight to edge $(v_i,v_j)$ as to $(v_j,v_i)$. This assumption is therefore
added to @{term "decTrail_eq_rev_incTrail"} and @{term "incTrail_eq_rev_decTrail"}. \<close>

lemma(in pair_sym_digraph) decTrail_eq_rev_incTrail:
  assumes "\<forall> v\<^sub>1 v\<^sub>2. w (v\<^sub>1,v\<^sub>2) = w(v\<^sub>2,v\<^sub>1)" 
  shows "decTrail G w es \<longleftrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es))"
    (*<*)using decTrail_implies_rev_incTrail incTrail_implies_rev_decTrail assms by blast(*>*)

lemma(in pair_sym_digraph) incTrail_eq_rev_decTrail:
  assumes "\<forall> v\<^sub>1 v\<^sub>2. w (v\<^sub>1,v\<^sub>2) = w(v\<^sub>2,v\<^sub>1)" 
  shows "incTrail G w es \<longleftrightarrow> decTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es))"
(*<*)proof-
  have "decTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es)) \<longleftrightarrow> incTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es))))"
    using assms decTrail_implies_rev_incTrail incTrail_implies_rev_decTrail by blast
  moreover have "(rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es)))) = es" 
  proof-
    have "(rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es)))) = (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) (rev (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es))))" 
      using rev_map by blast
    moreover have "(\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) \<circ> (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) = id " by auto 
    ultimately show ?thesis 
      by (simp add: \<open>(\<lambda>(v\<^sub>1, v\<^sub>2). (v\<^sub>2, v\<^sub>1)) \<circ> (\<lambda>(v\<^sub>1, v\<^sub>2). (v\<^sub>2, v\<^sub>1)) = id\<close>)
  qed
  ultimately show "incTrail G w es \<longleftrightarrow> decTrail G w (rev (map (\<lambda>(v\<^sub>1,v\<^sub>2). (v\<^sub>2,v\<^sub>1)) es))"
    by auto
qed(*>*)

subsection "Weighted Graphs"

text \<open> \label{localeSurjective} We add the locale @{text "weighted_pair_graph"} 
on top of the locale @{locale "pair_graph"} introduced in @{text "Graph_Theory"}. A  @{locale "pair_graph"} is a 
finite, loop free and symmetric graph. We do not restrict the types of vertices and edges but impose 
the condition that they have to be a linear order.

 Furthermore, all weights have to be integers between 0 and $\lfloor\frac{q}{2}\rfloor$ where 0 is 
used as a special value to indicate that there is no edge at that position. Since the 
range of the weight function is in the reals, the set of natural numbers
\mbox{@{text "{1,..,card (parcs G) div 2}"}} has to be casted into a set of reals. This is realized by taking the image
of the function @{text real} that casts a natural number to a real.  \<close>

locale weighted_pair_graph = pair_graph "(G:: ('a::linorder) pair_pre_digraph)" for G +
  fixes w :: "('a\<times>'a) weight_fun"
  assumes dom: "e \<in> parcs G \<longrightarrow> w e \<in> real ` {1..card (parcs G) div 2}" 
      and vert_ge: "card (pverts G) \<ge> 1" 
(*<*)
context weighted_pair_graph 
begin
(*>*)
text \<open> We introduce some useful abbreviations, according to the ones in Section \ref{Prelim}  \<close>

abbreviation(in weighted_pair_graph) "q \<equiv> card (parcs G)"
abbreviation(in weighted_pair_graph) "n \<equiv> card (pverts G)"
abbreviation(in weighted_pair_graph) "W \<equiv> {1..q div 2}"

text \<open>Note an important difference between Section \ref{PaperProof} and our formalization. Although 
a @{locale "weighted_pair_graph"} is symmetric, the edge set contains both ``directions" of an edge, 
i.e., $(v_1,v_2)$ and $(v_2,v_1)$ are both in @{term "parcs G"}. Thus, the maximum number of edges (in the 
case that the graph is complete) is $n\cdot(n-1)$ and not $\frac{n\cdot(n-1)}{2}$. Another consequence is that
the number $q$ of edges is always even. \<close>

lemma (in weighted_pair_graph) max_arcs: 
  shows "card (parcs G) \<le> n*(n-1)"
(*<*)proof-
  have "parcs G \<subseteq> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2}" 
    by (simp add: pair_no_loops prod.case_eq_if subsetI)
  moreover have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} = n*(n-1)" 
  proof-
    have "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} = {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
    proof
      show "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} \<subseteq> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
      proof
        fix x 
        assume a0: "x \<in> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2}"
        then have "x \<in> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G}" by blast
        moreover have "x \<notin> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}" using a0 by blast
        ultimately show "x \<in> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
          by blast
      qed
    next
      show "{v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}
                \<subseteq> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2}"
        by blast
    qed
    moreover have "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} \<subseteq> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G}" by blast
    moreover have "finite {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}" 
      using calculation(2) finite_subset by fastforce
    ultimately have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} 
                   = card ({v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G}) - card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
      by (simp add: card_Diff_subset)
    moreover have "card {v\<^sub>1. v\<^sub>1 \<in> pverts G} = n" by auto
    moreover have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} = card {v\<^sub>1. v\<^sub>1 \<in> pverts G}" 
    proof-
      have "inj_on (\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}" 
        by (smt Product_Type.Collect_case_prodD inj_onI prod.case_eq_if prod.collapse)
      moreover have "(\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) ` {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} = {v\<^sub>1. v\<^sub>1 \<in> pverts G}" by auto
      ultimately have "bij_betw (\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} {v\<^sub>1. v\<^sub>1 \<in> pverts G}" 
        by (simp add: bij_betw_def)
      then show ?thesis 
        using bij_betw_same_card by auto
    qed
    ultimately have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} = n*n - n" by auto
    then show ?thesis 
      by (simp add: diff_mult_distrib2)
  qed
  moreover have "finite {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2}" 
  proof-
    have "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} \<subseteq> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>1. v\<^sub>1 \<in> pverts G}" by auto
    moreover have "finite {v\<^sub>1. v\<^sub>1 \<in> pverts G}" by auto
    ultimately show ?thesis by (simp add: finite_subset)
  qed
  ultimately show ?thesis using card_mono by fastforce
qed

lemma card_W:
  shows "card (real ` W) = q div 2" 
proof-
  have "card W = q div 2" by simp
  moreover have "card (image real W) = card W" 
    using card_image inj_on_of_nat by blast
  ultimately show ?thesis by simp
qed

lemma strict_induct:
  assumes base: "P 0"
    and step: "\<And>i. (\<forall>j. j < Suc i \<longrightarrow> P j) \<Longrightarrow> P (Suc i)"
  shows "P i"
  by (metis gr0_implies_Suc infinite_descent0 local.base local.step nat_induct)

lemma aux_even_arcs:
  shows "\<forall> E:: ('a\<times>'a) set. card E = k \<longrightarrow> (\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> E \<and> ((e\<^sub>1,e\<^sub>2) \<in> E \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> E)) \<longrightarrow> even k" 
proof(rule strict_induct)
  show "\<forall> E:: ('a\<times>'a) set. card E = 0 \<longrightarrow> (\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> E \<and> ((e\<^sub>1,e\<^sub>2) \<in> E \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> E)) \<longrightarrow> even 0" by auto
next
  fix i 
  assume IH: "(\<forall>j. j < Suc i \<longrightarrow> (\<forall> E:: ('a\<times>'a) set. card E = j \<longrightarrow> (\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> E \<and> ((e\<^sub>1,e\<^sub>2) \<in> E \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> E)) \<longrightarrow> even j))" 
  show "\<forall> E:: ('a\<times>'a) set. card E = Suc i \<longrightarrow> (\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> E \<and> ((e\<^sub>1,e\<^sub>2) \<in> E \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> E)) \<longrightarrow> even (Suc i)"
  proof safe
    fix E :: "('a\<times>'a) set"
    assume a0: "card E = Suc i" and a1: "(\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> E \<and> ((e\<^sub>1,e\<^sub>2) \<in> E \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> E))"
    show "even (Suc i)"
    proof(cases)
      assume a2: "i < 1" 
      then have "i = 0" by blast
      then obtain x\<^sub>1 x\<^sub>2 where f0: "E = {(x\<^sub>1,x\<^sub>2)}" 
        using a0 card_1_singletonE by fastforce
      then have "(x\<^sub>2,x\<^sub>1) \<in> E" 
        using a1 by auto
      then have "card E \<ge> 2" 
        using f0 a1 by blast 
      then have "False" using a0 by (simp add: \<open>i = 0\<close>)
      then show "even (Suc i)" by simp
    next
      assume a2: "\<not>(i < 1)" 
      then have f0: "i \<ge> 1" by auto
      then have IH2: "card E = i - 1 \<longrightarrow> (\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> E \<and> ((e\<^sub>1,e\<^sub>2) \<in> E \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> E)) \<longrightarrow> even (i-1)" 
        for E:: "('a\<times>'a) set" using IH diff_less_Suc by blast
      then obtain x\<^sub>1 x\<^sub>2 where "(x\<^sub>1,x\<^sub>2) \<in> E" 
        by (metis Suc_le_eq a0 card_empty card_mono finite.intros(1) gr_implies_not0 prod.collapse subset_eq)
      then have "(x\<^sub>2,x\<^sub>1) \<in> E" using a1 by blast
      then have "card (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) = i - 1 \<longrightarrow> (\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> ((e\<^sub>1,e\<^sub>2) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}))) \<longrightarrow> even (i-1)"
        using IH2[of "E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}"] by auto
      moreover have "card (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) = i - 1" 
        by (metis \<open>(x\<^sub>2, x\<^sub>1) \<in> E\<close> a0 a1 card_Diff_insert card_Diff_singleton card_infinite diff_Suc_1 empty_iff insert_iff nat.simps(3) snd_conv)
      moreover have "(\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> ((e\<^sub>1,e\<^sub>2) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)})))" 
      proof (intro allI)
        fix e\<^sub>1 e\<^sub>2
        have "(e\<^sub>1,e\<^sub>1) \<notin> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)})" using a1 by blast
        moreover have "((e\<^sub>1,e\<^sub>2) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}))" using a1 by auto
        ultimately show "(e\<^sub>1,e\<^sub>1) \<notin> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> ((e\<^sub>1,e\<^sub>2) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> (E-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}))" by auto
      qed
      ultimately have "even (i-1)" by auto
      then show "even (Suc i)" using a2 dvd_diffD1 even_Suc f0 by blast
    qed
  qed
qed(*>*)

lemma (in weighted_pair_graph) even_arcs: 
shows "even q"
(*<*)proof-
  have "card (parcs G) = q" by simp
  moreover have "(\<forall>e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>1) \<notin> (parcs G) \<and> ((e\<^sub>1,e\<^sub>2) \<in> (parcs G) \<longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> (parcs G)))" 
    using adj_not_same graph_symmetric by blast
  ultimately show "even q" 
    using aux_even_arcs by blast
qed

end (*context weighted_pair_graph*)
(*>*)
text \<open> The below sublocale @{text "distinct_weighted_pair_graph"} refines
@{text "weighted_pair_graph"}. The condition 
@{text "zero"} fixes the meaning of 0.
The weight function is defined on the set of all vertices but since self loops are not allowed; 
we use 0 as a special value to indicate the unavailability of the edge. 
The second condition @{text "distinct"} enforces that no two edges can have the same weight. There
are some exceptions however captured in the statement @{text "(v\<^sub>1 = u\<^sub>2 \<and> v\<^sub>2 = u\<^sub>1) \<or> (v\<^sub>1 = u\<^sub>1 \<and> v\<^sub>2 = u\<^sub>2)"}.
Firstly, $(v_1,v_2)$ should have the same weight as $(v_2,v_1)$. Secondly, $w(v_1,v_2)$ has the
same value as $w(v_1,v_2)$. Note that both edges being self loops resulting in them both having 
weight 0 is prohibited by condition @{text "zero"}.
Our decision to separate these two conditions from the ones in @{text "weighted_pair_graph"}
instead of making one locale of its own is two-fold: On the one hand, there are scenarios where 
distinctiveness is not wished for. On the other hand, 0 might not be available as a special value.
\<close>

locale distinct_weighted_pair_graph = weighted_pair_graph + 
  assumes zero: "\<forall> v\<^sub>1 v\<^sub>2. (v\<^sub>1,v\<^sub>2) \<notin> parcs G \<longleftrightarrow> w (v\<^sub>1,v\<^sub>2) = 0"
      and distinct: "\<forall> (v\<^sub>1,v\<^sub>2) \<in> parcs G. \<forall> (u\<^sub>1,u\<^sub>2) \<in> parcs G. 
      ((v\<^sub>1 = u\<^sub>2 \<and> v\<^sub>2 = u\<^sub>1) \<or> (v\<^sub>1 = u\<^sub>1 \<and> v\<^sub>2 = u\<^sub>2)) \<longleftrightarrow> w (v\<^sub>1,v\<^sub>2) = w (u\<^sub>1,u\<^sub>2)" 

(*<*)context distinct_weighted_pair_graph
begin

lemma undirected:
  assumes "v\<^sub>1 \<in> pverts G" and "v\<^sub>2 \<in> pverts G" 
  shows "w (v\<^sub>1,v\<^sub>2) = w (v\<^sub>2,v\<^sub>1)"
  using distinct assms 
  by (smt graph_symmetric old.prod.case zero)

lemma weight_zero [simp]:
  assumes "v\<^sub>1 \<notin> pverts G \<or> v\<^sub>2 \<notin> pverts G"
  shows "w (v\<^sub>1,v\<^sub>2) = 0"
  using assms zero in_arcsD1 in_arcsD2 by blast

lemma weight_not_zero [simp]:
  assumes "v\<^sub>1 \<in> pverts G" and "v\<^sub>2 \<in> pverts G" and "(v\<^sub>1,v\<^sub>2) \<in> parcs G"
  shows "w (v\<^sub>1,v\<^sub>2) \<noteq> 0" 
  using assms atLeast0LessThan zero distinct by auto

lemma weight_not_zero_implies_arc [simp]: 
  assumes "w (v\<^sub>1,v\<^sub>2) = k" and "k \<noteq> 0" 
  shows "(v\<^sub>1, v\<^sub>2) \<in> parcs G" 
  using assms dom zero by blast

lemma weight_unique:
  assumes "w (v\<^sub>1,v\<^sub>2) = k" and "(v\<^sub>1,v\<^sub>2) \<noteq> (u\<^sub>1,u\<^sub>2)" and "(v\<^sub>1,v\<^sub>2) \<noteq> (u\<^sub>2,u\<^sub>1)" and "k \<noteq> 0" 
  shows "w (u\<^sub>1,u\<^sub>2) \<noteq> k" 
proof-
  have "(v\<^sub>1, v\<^sub>2) \<in> parcs G" using assms weight_not_zero_implies_arc by auto
  then show ?thesis 
    by (smt assms case_prodE distinct fst_conv snd_conv weight_not_zero_implies_arc)
qed

lemma aux_restricted_weight_fun_card2: 
  fixes k :: nat
  shows "\<forall> i. i \<le> k \<longrightarrow> (\<forall>(A::('a\<times>'a) set). finite A \<and> card A = i \<and> (\<forall>x. (x,x) \<notin> A) \<and> (\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A) \<longrightarrow> card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2)" 
proof(induction k)
  show "\<forall> i. i \<le> 0 \<longrightarrow> (\<forall>(A::('a\<times>'a) set). finite A \<and> card A = i  \<and> (\<forall>x. (x,x) \<notin> A) \<and> (\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A) \<longrightarrow> card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2)" 
  proof safe
    fix A ::"('a\<times>'a) set"
    assume "finite A" and "card A = 0"
    then have "A = {}" using card_0_eq by blast
    then show "card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = 0 div 2" by simp
  qed
next
  fix k
  assume IH: "\<forall> i. i \<le> k \<longrightarrow> (\<forall>(A::('a\<times>'a) set).  finite A \<and> card A = i \<and> (\<forall>x. (x,x) \<notin> A) \<and> (\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A) \<longrightarrow> card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2)"
  then have "i \<le> k \<longrightarrow> (\<forall>(A::('a\<times>'a) set). finite A \<and> card A = i \<and> (\<forall>x. (x,x) \<notin> A) \<and> (\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A) \<longrightarrow> card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2)" 
    for i::nat  by blast
  then have IH2: " i \<le> k \<longrightarrow> (finite A \<and> card A = i \<and> (\<forall>x. (x,x) \<notin> A) \<and> (\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A) \<longrightarrow> card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2)" 
    for i::nat and A::"('a\<times>'a) set" by blast
  show "\<forall> i. i \<le> (Suc k) \<longrightarrow> (\<forall>(A::('a\<times>'a) set). finite A \<and> card A = i \<and> (\<forall>x. (x,x) \<notin> A) \<and> (\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A) \<longrightarrow> card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2)" 
  proof (rule allI, rule impI, rule allI, rule impI)
    fix i
    fix  A ::"('a\<times>'a) set"
    assume a0: "i \<le> Suc k" 
    assume a2: "finite A \<and> card A = i \<and> (\<forall>x. (x, x) \<notin> A) \<and> (\<forall>x y. (x, y) \<in> A \<longrightarrow> (y, x) \<in> A)"
    then have a1: "finite A" and a3: "(\<forall>x. (x,x) \<notin> A)" and a4: "(\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A)" apply blast 
      apply (simp add: \<open>finite A \<and> card A = i \<and> (\<forall>x. (x, x) \<notin> A) \<and> (\<forall>x y. (x, y) \<in> A \<longrightarrow> (y, x) \<in> A)\<close>)
      using \<open>finite A \<and> card A = i \<and> (\<forall>x. (x, x) \<notin> A) \<and> (\<forall>x y. (x, y) \<in> A \<longrightarrow> (y, x) \<in> A)\<close> by blast
    show "card {(p1, p2). (p1, p2) \<in> A \<and> p2 < p1} = i div 2"
    proof(rule disjE)
      show "i \<ge> 1 \<or> i = 0" by auto
    next
      assume a0b: "i = 0" 
      then show "card {(p1, p2). (p1, p2) \<in> A \<and> p2 < p1} = i div 2" 
        using a2 by force
    next
      assume a0b: "i \<ge> 1" 
    then have "\<exists>x\<^sub>1 x\<^sub>2. (x\<^sub>1,x\<^sub>2) \<in> A \<and> (x\<^sub>2,x\<^sub>1) \<in> A" 
      by (metis One_nat_def Suc_n_not_le_n a0b a2 card.empty card_insert_disjoint card_le_Suc_iff equals0I le_eq_less_or_eq order.trans prod.collapse)
    then obtain x\<^sub>1 x\<^sub>2 where f0: "(x\<^sub>1,x\<^sub>2) \<in> A \<and> x\<^sub>1 < x\<^sub>2" by (metis a3 neqE)
    then have "finite (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)})" by (simp add: a1)
    moreover have "card (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) = i - 2" 
      using a1 a4 f0 a0 
      by (smt Diff_empty Suc_1 a2 card_Diff_insert diff_Suc_eq_diff_pred insert_absorb insert_iff insert_not_empty prod.inject)
    moreover have "(\<forall>y. (y,y) \<notin> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}))" 
      using a3 by auto
    moreover have "(\<forall>x y. (x,y) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<longrightarrow> (y,x) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}))" 
      using a4 by auto 
    ultimately have "card {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} = (i - 2) div 2" 
      using IH2[of "i-2" "(A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)})"] 
      by (metis (no_types, lifting) Suc_1 Suc_diff_Suc Suc_leD a0 a0b a2 aux_even_arcs card_Suc_Diff1 diff_Suc_1 f0 le_Suc_eq le_eq_less_or_eq odd_one)
    then have f1: "card {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} = i div 2 - 1" 
      using plus_1_eq_Suc by linarith
    moreover have f2: "{(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1} = {(x\<^sub>2,x\<^sub>1)}" 
    proof
      show "{(p1, p2). (p1, p2) \<in> {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1} \<subseteq> {(x\<^sub>2, x\<^sub>1)}"
      proof
        fix x 
        assume "x \<in> {(p1, p2). (p1, p2) \<in> {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1}"
        then have "x = (x\<^sub>2,x\<^sub>1)" 
          using f0 by auto
        then show "x \<in> {(x\<^sub>2, x\<^sub>1)}" by auto
      qed
      show "{(x\<^sub>2,x\<^sub>1)} \<subseteq> {(p1, p2). (p1, p2) \<in> {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1}" 
        by (simp add: f0)
    qed
    moreover have "card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} 
                 = card {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} + card {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1}"
    proof-
      have "{(p1,p2). (p1,p2) \<in> A \<and> p2 < p1}  
          = {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} \<union> {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1}" 
      proof
        show "{(p1,p2). (p1,p2) \<in> A \<and> p2 < p1}  
          \<subseteq> {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} \<union> {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1}" by auto
        show "{(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} \<union> {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1}
            \<subseteq> {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1}  " 
        proof
          fix x
          assume "x \<in> {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} \<union> {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1}"
          show "x \<in> {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} "  
            using Product_Type.Collect_case_prodD \<open>x \<in> {(p1, p2). (p1, p2) \<in> A - {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1} \<union> {(p1, p2). (p1, p2) \<in> {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1}\<close> a4 f0 by auto
        qed
      qed
      moreover have "{} = {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} \<inter> {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1}" 
      proof
        show "{} \<subseteq> {(p1, p2). (p1, p2) \<in> A - {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1} \<inter> {(p1, p2). (p1, p2) \<in> {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1}" by blast
      next
        show "{(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} \<inter> {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1} \<subseteq> {}"
          by auto
      qed
      moreover have "finite {(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1}" 
      proof-
        have "{(p1,p2). (p1,p2) \<in> (A-{(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)}) \<and> p2 < p1} \<subseteq> {x. x \<in> A}" by auto
        moreover have "finite {x. x \<in> A}" using a1 by auto
        ultimately show ?thesis 
          by (simp add: finite_subset)
      qed
      moreover have "finite {(p1,p2). (p1,p2) \<in> {(x\<^sub>1,x\<^sub>2),(x\<^sub>2,x\<^sub>1)} \<and> p2 < p1}" 
        using card_eq_0_iff f2 by fastforce
      ultimately show ?thesis 
        using card_Un_disjoint by (metis (no_types, lifting))
    qed
    ultimately have "card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2 - 1 + 1" by simp
    then have "card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2" 
      using Suc_diff_Suc \<open>card {(p1, p2). (p1, p2) \<in> A - {(x\<^sub>1, x\<^sub>2), (x\<^sub>2, x\<^sub>1)} \<and> p2 < p1} = (i - 2) div 2\<close> 
          a0b a2 add.commute aux_even_arcs f1 le_add_diff_inverse le_eq_less_or_eq odd_one one_add_one plus_1_eq_Suc 
      by (metis (no_types, lifting) div2_Suc_Suc ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
    then show "card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = i div 2" 
      using \<open>finite A \<and> card A = i \<and> (\<forall>x. (x, x) \<notin> A) \<and> (\<forall>x y. (x, y) \<in> A \<longrightarrow> (y, x) \<in> A)\<close> a2 by linarith
  qed
qed
qed

lemma restricted_weight_fun_card:
  shows "card {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1} = q div 2" 
proof-
  have "(\<forall>(A::('a\<times>'a) set). finite A \<and> card A = q \<and> (\<forall>x. (x,x) \<notin> A) \<and> (\<forall>x y. (x,y) \<in> A \<longrightarrow> (y,x) \<in> A) \<longrightarrow> card {(p1,p2). (p1,p2) \<in> A \<and> p2 < p1} = q div 2)" 
    using aux_restricted_weight_fun_card2 by auto
  then have "finite (parcs G) \<and> card (parcs G) = q \<and> (\<forall>x. (x,x) \<notin> (parcs G)) \<and> (\<forall>x y. (x,y) \<in> (parcs G) \<longrightarrow> (y,x) \<in> (parcs G)) \<longrightarrow> 
              card {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1} = q div 2" by auto
  moreover have "finite (parcs G) \<and> card (parcs G) = q \<and> (\<forall>x. (x,x) \<notin> (parcs G)) \<and> (\<forall>x y. (x,y) \<in> (parcs G) \<longrightarrow> (y,x) \<in> (parcs G))" 
    using adj_not_same arcs_symmetric pair_finite_arcs by blast
  ultimately show ?thesis by auto
qed

lemma surjective_iff_injective_gen_le:
  assumes "finite S" and "finite T" and "card T \<le> card S" and "f ` S \<subseteq> T" and "inj_on f S"
  shows "(\<forall>y \<in> T. \<exists>x \<in> S. f x = y)"
  by (meson antisym assms card_inj_on_le surjective_iff_injective_gen)(*>*)

text \<open> One important step in our formalization is to show that the weight function is surjective. However, having two 
elements of the domain (edges) being mapped to the same element of the codomain (weight) makes 
the proof complicated. We therefore first prove that the weight function is surjective on a restricted
set of edges. Here we use the fact that there is a linear order on vertices by only considering edges
were the first endpoint is bigger than the second. 

Then, the surjectivity of $w$ is relatively simple to show. Note that we could also have assumed surjectivity in 
@{locale distinct_weighted_pair_graph} and shown that distinctiveness follows from it. However,
distinctiveness is the more natural assumption that is more likely to appear in any application
of ordered trails. \<close>

lemma(in distinct_weighted_pair_graph) restricted_weight_fun_surjective:  
  shows "\<forall>k \<in> W. \<exists>(v\<^sub>1,v\<^sub>2) \<in> {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}. w (v\<^sub>1,v\<^sub>2) = k"
(*<*)proof(rule disjE)
  show "n = 1 \<or> n \<ge> 2" using vert_ge by auto
next
  assume "n = 1" 
  then show "\<forall>y \<in> W. \<exists>(v\<^sub>1,x\<^sub>2) \<in> {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}. w (v\<^sub>1,x\<^sub>2) = y" 
    using max_arcs by auto
next
  assume "n \<ge> 2" 
  then have "n*(n-1) div 2 \<ge> 1" 
    apply (induction n)
    apply simp
    by (metis Suc_1 Suc_eq_plus1 add.commute diff_Suc_1 diff_is_0_eq dvd_div_mult_self even_Suc even_mult_iff le_iff_add mult_eq_0_iff not_less_eq_eq)
  then have "finite {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}" 
    using restricted_weight_fun_card vert_ge 
    by (metis (no_types, lifting) Product_Type.Collect_case_prodD finite_subset pair_finite_arcs prod.collapse subsetI)
  moreover have "finite W" by auto
  moreover have "inj_on w {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}" 
  proof
    fix v u
    assume a0: "v \<in> {(p1, p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}" 
       and a1: "u \<in> {(p1, p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}" and a2: "w v = w u"
    obtain v\<^sub>1 v\<^sub>2 where v_def: "v = (v\<^sub>1,v\<^sub>2)" using a0 by blast
    obtain u\<^sub>1 u\<^sub>2 where u_def: "u = (u\<^sub>1,u\<^sub>2)" using a1 by blast
    have "((v\<^sub>1 = u\<^sub>1 \<and> v\<^sub>2 = u\<^sub>2) \<or> (v\<^sub>1 = u\<^sub>2 \<and> v\<^sub>2 = u\<^sub>1) \<or> (v\<^sub>1 = v\<^sub>2 \<and> u\<^sub>1 = u\<^sub>2))" 
      by (metis (no_types, lifting) Product_Type.Collect_case_prodD a1 a2 fst_conv snd_conv weight_unique u_def v_def zero)
    moreover have "v\<^sub>2 < v\<^sub>1" using v_def a0 by auto
    moreover have "u\<^sub>2 < u\<^sub>1" using u_def a1 by auto
    ultimately have "(v\<^sub>1 = u\<^sub>1 \<and> v\<^sub>2 = u\<^sub>2)" by auto
    then show "v = u" by (simp add: u_def v_def)
  qed
  moreover have "card {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1} \<ge> card (real ` W)" 
    using card_W max_arcs restricted_weight_fun_card by linarith
  moreover have "w ` {(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1} \<subseteq> (real ` W)" 
  proof-
    have "{y. \<exists>x\<in>{(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}. y = w x} \<subseteq> (real ` W)" 
    proof
      fix y
      assume a0: "y \<in> {y. \<exists>x\<in>{(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}. y = w x}"
      then obtain p1 p2 where f1: "(p1,p2) \<in> (parcs G) \<and> p2 < p1 \<and> y = w (p1,p2)" by auto
      then have "y \<noteq> 0" using dom zero by auto
      moreover have "y \<in> (real ` {1..q div 2})" using dom f1 calculation weight_not_zero_implies_arc by blast
      ultimately show "y \<in> (real ` W)" 
        using add_diff_cancel_left' by fastforce
    qed
    then show ?thesis by blast
  qed
  ultimately show ?thesis using surjective_iff_injective_gen_le[of "{(p1,p2). (p1,p2) \<in> (parcs G) \<and> p2 < p1}" "real ` W" w] by auto 
qed(*>*)

lemma(in distinct_weighted_pair_graph) weight_fun_surjective:
  shows "(\<forall>k \<in> W. \<exists>(v\<^sub>1,v\<^sub>2) \<in> (parcs G). w (v\<^sub>1,v\<^sub>2) = k)" 
(*<*) using restricted_weight_fun_surjective 
  by (metis (no_types, lifting) case_prodE mem_Collect_eq restricted_weight_fun_card)

lemma weight_different:
  assumes "y \<noteq> (v\<^sub>1,v\<^sub>2)" and "y \<noteq> (v\<^sub>2,v\<^sub>1)" and "w (v\<^sub>1,v\<^sub>2) = k" and "(v\<^sub>1,v\<^sub>2) \<in> parcs G" 
  shows "w y \<noteq> k" 
  by (metis (no_types, lifting) assms weight_unique zero prod.collapse) 

end

instantiation prod :: (linorder,linorder) linorder begin
  definition "less_eq_prod \<equiv> \<lambda>(x\<^sub>1,x\<^sub>2) (y\<^sub>1,y\<^sub>2). x\<^sub>1 < y\<^sub>1 \<or> x\<^sub>1 = y\<^sub>1 \<and> x\<^sub>2 \<le> y\<^sub>2"
  definition "less_prod \<equiv> \<lambda>(x\<^sub>1,x\<^sub>2) (y\<^sub>1,y\<^sub>2). x\<^sub>1 < y\<^sub>1 \<or> x\<^sub>1 = y\<^sub>1 \<and> x\<^sub>2 < y\<^sub>2"
    instance by standard (auto simp add: less_eq_prod_def less_prod_def) 
end

definition set_to_list :: "('a::linorder\<times>'a) set \<Rightarrow> ('a\<times>'a) list"
  where "set_to_list A = sorted_list_of_set A" 

lemma set_set_to_list:
  shows "finite A \<Longrightarrow> set (set_to_list A) = A"
  by (simp add: set_to_list_def)

lemma set_to_list_length:
  assumes "A \<noteq> {}" and "finite A"
  shows "1 \<le> length (set_to_list A)"
  using assms(1) assms(2) linorder_not_less set_set_to_list by fastforce

lemma set_to_list_mono:
  assumes "a \<in> A" and "finite A"
  shows "a \<in> set (set_to_list A)" 
  by (simp add: assms(1) assms(2) set_set_to_list)(*>*)

subsection \<open> Computing a Longest Ordered Trail \<close>

text \<open>\label{compAlgo}We next formally verify Algorithm \ref{algo} and compute longest ordered trails. To this end, 
we introduce the function @{text "findEdge"} to find an edge in a list of edges by its weight. \<close>

fun findEdge :: "('a\<times>'a) weight_fun \<Rightarrow> ('a\<times>'a) list \<Rightarrow> real \<Rightarrow> ('a\<times>'a)" where
"findEdge f [] k = undefined" |
"findEdge f (e#es) k = (if f e = k then e else findEdge f es k)" 

(*<*)context distinct_weighted_pair_graph
begin

lemma aux_findEdge_success:
  assumes "a \<ge> 1"
  shows "\<forall>ys. k \<in> W \<and> w (x\<^sub>1,x\<^sub>2) = k \<and> length ys = a \<and> ((x\<^sub>1,x\<^sub>2) \<in> set ys \<or> (x\<^sub>2,x\<^sub>1) \<in> set ys) \<longrightarrow>
(\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>1,x\<^sub>2)#xs) k)) \<or> (\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>2,x\<^sub>1)#xs) k))"
proof(rule Nat.nat_induct_at_least[of 1 a])
  show "a \<ge> 1" using assms by simp
next
  show "\<forall>ys. k \<in> W \<and> w (x\<^sub>1, x\<^sub>2) = real k \<and> length ys = 1 \<and> ((x\<^sub>1,x\<^sub>2) \<in> set ys \<or> (x\<^sub>2,x\<^sub>1) \<in> set ys) \<longrightarrow>
    (\<exists>xs. findEdge w ys k = findEdge w ((x\<^sub>1, x\<^sub>2) # xs) k) \<or> (\<exists>xs. findEdge w ys k = findEdge w ((x\<^sub>2, x\<^sub>1) # xs) k)"
  proof(rule allI, rule impI)
    fix ys
    assume a0: "k \<in> W \<and> w (x\<^sub>1, x\<^sub>2) = real k \<and> length ys = 1 \<and> ((x\<^sub>1,x\<^sub>2) \<in> set ys \<or> (x\<^sub>2,x\<^sub>1) \<in> set ys)" 
    then have "hd ys = (x\<^sub>1,x\<^sub>2) \<or> hd ys = (x\<^sub>2,x\<^sub>1)"
      by (smt One_nat_def Suc_length_conv hd_Cons_tl length_0_conv list.sel(3) list.set(1) list.set(2) singletonD)
    then show "(\<exists>xs. findEdge w ys k = findEdge w ((x\<^sub>1, x\<^sub>2) # xs) k) \<or> (\<exists>xs. findEdge w ys k = findEdge w ((x\<^sub>2, x\<^sub>1) # xs) k)"
      by (metis One_nat_def a0 hd_Cons_tl length_0_conv nat.simps(3))
  qed
next
  fix a
  assume IH: "\<forall>ys. k \<in> W \<and> w (x\<^sub>1,x\<^sub>2) = k \<and> length ys = a \<and> ((x\<^sub>1,x\<^sub>2) \<in> set ys \<or> (x\<^sub>2,x\<^sub>1) \<in> set ys) \<longrightarrow>
(\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>1,x\<^sub>2)#xs) k)) \<or> (\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>2,x\<^sub>1)#xs) k))"
  show "\<forall>ys. k \<in> W \<and> w (x\<^sub>1,x\<^sub>2) = k \<and> length ys = (Suc a) \<and> ((x\<^sub>1,x\<^sub>2) \<in> set ys \<or> (x\<^sub>2,x\<^sub>1) \<in> set ys) \<longrightarrow>
(\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>1,x\<^sub>2)#xs) k)) \<or> (\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>2,x\<^sub>1)#xs) k))"
  proof(rule allI, rule impI)
    fix ys
    assume a0: "k \<in> W \<and> w (x\<^sub>1,x\<^sub>2) = k \<and> length ys = (Suc a) \<and> ((x\<^sub>1,x\<^sub>2) \<in> set ys \<or> (x\<^sub>2,x\<^sub>1) \<in> set ys)"
    show "(\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>1,x\<^sub>2)#xs) k)) \<or> (\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>2,x\<^sub>1)#xs) k))"
    proof(rule disjE)
      show "((hd ys) = (x\<^sub>1,x\<^sub>2) \<or> (hd ys) = (x\<^sub>2,x\<^sub>1)) \<or> ((hd ys) \<noteq> (x\<^sub>1,x\<^sub>2) \<and> (hd ys) \<noteq> (x\<^sub>2,x\<^sub>1))" by auto
    next
      assume "hd ys = (x\<^sub>1,x\<^sub>2) \<or> (hd ys) = (x\<^sub>2,x\<^sub>1)"
      then show "(\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>1,x\<^sub>2)#xs) k)) \<or> (\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>2,x\<^sub>1)#xs) k))"
        by (metis a0 hd_Cons_tl length_0_conv nat.simps(3))
    next
      assume "(hd ys) \<noteq> (x\<^sub>1,x\<^sub>2) \<and> (hd ys) \<noteq> (x\<^sub>2,x\<^sub>1)"
      moreover have "w (x\<^sub>1,x\<^sub>2) \<noteq> 0" 
        using a0 weighted_pair_graph_axioms by auto
      ultimately have "w (hd ys) \<noteq> k" using a0 zero distinct weight_different 
        by (metis (no_types, lifting))
      then have "(findEdge w ys k) = (findEdge w (tl ys) k)"
        by (metis a0 findEdge.elims length_0_conv list.sel(1) list.sel(3) nat.simps(3)) 
      then show "(\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>1,x\<^sub>2)#xs) k)) \<or> (\<exists>xs. (findEdge w ys k) = (findEdge w ((x\<^sub>2,x\<^sub>1)#xs) k))"
        using IH 
        by (metis a0 add_diff_cancel_left' hd_Cons_tl length_0_conv length_tl nat.simps(3) plus_1_eq_Suc set_ConsD)
    qed
  qed
qed
(*>*)
text \<open> Function @{text findEdge} will correctly return the edge whose weight is $k$. We do not care in which order the endpoints
are found, i.e. whether $(v_1,v_2)$ or $(v_2,v_1)$ is returned.  \<close>

lemma(in distinct_weighted_pair_graph) findEdge_success:
  assumes "k \<in> W" and "w (v\<^sub>1,v\<^sub>2) = k" and "(parcs G) \<noteq> {}" 
  shows "(findEdge w (set_to_list (parcs G)) k) = (v\<^sub>1,v\<^sub>2) 
        \<or> (findEdge w (set_to_list (parcs G)) k) = (v\<^sub>2,v\<^sub>1)"
(*<*)proof-
  have "(\<exists>xs. (findEdge w (set_to_list (parcs G)) k) = (findEdge w ((v\<^sub>1,v\<^sub>2)#xs) k))
      \<or> (\<exists>xs. (findEdge w (set_to_list (parcs G)) k) = (findEdge w ((v\<^sub>2,v\<^sub>1)#xs) k))" 
  proof-
    have f0: "finite (parcs G)" using local.finite_arcs by auto
    then have "1 \<le> length (set_to_list (parcs G))" using assms by (meson set_to_list_length)
    moreover have "(v\<^sub>1,v\<^sub>2) \<in> set (set_to_list (parcs G))" using assms set_to_list_mono[of "(v\<^sub>1,v\<^sub>2)" "parcs G"] f0 by auto
    ultimately show ?thesis using aux_findEdge_success[of "length (set_to_list (arcs G))" k v\<^sub>1 v\<^sub>2] assms by simp
  qed
  moreover have "\<forall>xs. (findEdge w ((v\<^sub>1,v\<^sub>2)#xs) k) = (v\<^sub>1,v\<^sub>2)" by (simp add: assms(2))
  moreover have "\<forall>xs. (findEdge w ((v\<^sub>2,v\<^sub>1)#xs) k) = (v\<^sub>2,v\<^sub>1)" 
    using assms(2) distinct_weighted_pair_graph.undirected distinct_weighted_pair_graph_axioms 
    by (metis (no_types, lifting) distinct findEdge.simps(2) in_arcsD1 in_arcsD2 undirected zero)
  ultimately show ?thesis by metis
qed

lemma findEdge_bound:
  assumes "k \<in> W" and "(parcs G) \<noteq> {}" 
  shows "fst (findEdge w (set_to_list (parcs G)) k) \<in> (pverts G)" 
    and "snd (findEdge w (set_to_list (parcs G)) k) \<in> (pverts G)"
proof-
  obtain v\<^sub>1 v\<^sub>2::'a where a0: "w (v\<^sub>1,v\<^sub>2) = k" using weight_fun_surjective assms by blast
  then have "v\<^sub>1 \<noteq> v\<^sub>2" 
    using assms pair_no_loops 
    by (metis adj_not_same atLeastAtMost_iff le_numeral_extra(2) of_nat_0 of_nat_eq_iff weight_not_zero_implies_arc)
  moreover have "(v\<^sub>1, v\<^sub>2) \<in> parcs G" using weight_not_zero_implies_arc assms by (simp add: a0)
  ultimately have f0: "(findEdge w (set_to_list (parcs G)) k) = (v\<^sub>1,v\<^sub>2) \<or> (findEdge w (set_to_list (parcs G)) k) = (v\<^sub>2,v\<^sub>1)" 
    using findEdge_success assms a0 by fastforce
  then show "fst (findEdge w (set_to_list (parcs G)) k) \<in> (pverts G)"
        and "snd (findEdge w (set_to_list (parcs G)) k) \<in> (pverts G)" 
    using a0 assms apply auto[1] 
    by (metis \<open>(v\<^sub>1, v\<^sub>2) \<in> parcs G\<close> f0 head_in_verts in_arcsD1 snd_conv)
qed 

lemma findEdge_surjective:
  assumes "(Suc i) \<in> W"
  shows "w (fst (findEdge w (set_to_list (parcs G)) (Suc i)), snd(findEdge w (set_to_list (parcs G)) (Suc i))) = (Suc i)"
    and "w (snd (findEdge w (set_to_list (parcs G)) (Suc i)), fst(findEdge w (set_to_list (parcs G)) (Suc i))) = (Suc i)"
proof- 
  obtain v\<^sub>1 v\<^sub>2 where f0: "w (v\<^sub>1,v\<^sub>2) = (Suc i)" using weight_fun_surjective assms by blast
  then have "v\<^sub>1 \<noteq> v\<^sub>2" 
    using pair_no_loops of_nat_neq_0 weight_not_zero_implies_arc adj_not_same by blast
  moreover have "v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G" using f0 of_nat_neq_0 of_nat_0_eq_iff assms 
    by (metis Zero_not_Suc of_nat_eq_0_iff distinct_weighted_pair_graph.weight_zero distinct_weighted_pair_graph_axioms with_proj_simps(1))
  moreover have "parcs G \<noteq> {}" using f0 calculation weight_not_zero_implies_arc by fastforce
  moreover have "(v\<^sub>1, v\<^sub>2) \<in> parcs G" using weight_not_zero_implies_arc assms by (simp add: f0)
  ultimately have f1: "(findEdge w (set_to_list (parcs G)) (Suc i)) = (v\<^sub>1,v\<^sub>2) \<or> (findEdge w (set_to_list (parcs G)) (Suc i)) = (v\<^sub>2,v\<^sub>1)" 
    using findEdge_success[of "Suc i" v\<^sub>1 v\<^sub>2] assms f0 by auto
  then show "w (fst (findEdge w (set_to_list (parcs G)) (Suc i)), snd(findEdge w (set_to_list (parcs G)) (Suc i))) = (Suc i)"
        and "w (snd (findEdge w (set_to_list (parcs G)) (Suc i)), fst(findEdge w (set_to_list (parcs G)) (Suc i))) = (Suc i)"
    using \<open>v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G\<close> distinct f0 undirected apply auto[1] 
    using \<open>v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G\<close> distinct f0 f1 undirected by auto
qed
 
end(*>*)

text \<open>We translate the notion of a labelling function $L^i(v)$ (see Definition \ref{Labelling}) into Isabelle.
Function @{text "getL G w"}, in short for get label, returns the length of the longest strictly decreasing
path starting at vertex $v$. In contrast to Definition \ref{Labelling} subgraphs are treated here implicitly. Intuitively,
this can be seen as adding edges to an empty graph in order of their weight. 
 \<close>

fun getL :: "('a::linorder) pair_pre_digraph \<Rightarrow> ('a\<times>'a) weight_fun 
             \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat" where
"getL g w 0 v = 0" |  
"getL g w (Suc i) v = (let (v\<^sub>1,v\<^sub>2) = (findEdge w (set_to_list (arcs g)) (Suc i)) in 
                      (if v = v\<^sub>1 then max ((getL g w i v\<^sub>2)+1) (getL g w i v) else 
                      (if v = v\<^sub>2 then max ((getL g w i v\<^sub>1)+1) (getL g w i v) else 
                       getL g w i v)))"

text \<open> To add all edges to the graph, set $i=|E|$. Recall that @{term "card (parcs g)"} $= 2*|E|$, 
as every edge appears twice. 
Then, iterate over all vertices and give back the
maximum length which is found by using @{text "getL G w"}. Since @{text "getL G w"} can also be used to get a longest 
strictly increasing trail ending at vertex $v$ the algorithm is not restricted to strictly decreasing trails. \<close>

definition getLongestTrail :: 
"('a::linorder) pair_pre_digraph \<Rightarrow> ('a\<times>'a) weight_fun \<Rightarrow> nat" where
"getLongestTrail g w = 
Max (set [(getL g w (card (parcs g) div 2) v) . v <- sorted_list_of_set (pverts g)])" 

text \<open> Exporting the algorithm into Haskell code results in a fully verified program to find a longest
strictly decreasing or strictly increasing trail. \<close>

export_code getLongestTrail in Haskell module_name LongestTrail

(*<*)context distinct_weighted_pair_graph
begin

lemma aux_getL:
  assumes "v \<noteq> fst (findEdge w (set_to_list (parcs G)) (Suc i))" and "v \<noteq> snd (findEdge w (set_to_list (parcs G)) (Suc i))"
  shows "getL G w (i+1) v = getL G w i v"
proof-
  have "\<exists>v\<^sub>1 v\<^sub>2. (findEdge w (set_to_list (parcs G)) (Suc i)) = (v\<^sub>1,v\<^sub>2)" by simp
  then obtain v\<^sub>1 v\<^sub>2 where f0: "(findEdge w (set_to_list (parcs G)) (Suc i)) = (v\<^sub>1,v\<^sub>2)" by blast
  then have "v \<noteq> v\<^sub>1 \<and> v \<noteq> v\<^sub>2" 
    using assms by auto 
  then show ?thesis using f0 getL.simps(2) 
    by (smt Suc_eq_plus1 old.prod.case with_proj_simps(2))
qed

lemma aux_correctness_case_endpoint1:
  assumes a0: "(Suc k) \<le> q div 2"
      and a1: "getL G w (Suc k) v\<^sub>1 = a"
      and a2: "(findEdge w (set_to_list (parcs G)) (Suc k)) = (v\<^sub>1,v\<^sub>2)"
      and IH: "\<forall>a v. k \<le> q div 2 \<longrightarrow> getL G w k v = a \<longrightarrow> (\<exists> xs. decTrail G w xs \<and> length xs = a 
            \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v))" 
    shows "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v\<^sub>1))" 
proof(rule disjE)
  have "getL G w (Suc k) v\<^sub>1 = max (getL G w k v\<^sub>2 + 1) (getL G w k v\<^sub>1)"
    using a2 by auto
  then show "getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>2 + 1 \<or> getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>1" using a2 by linarith
next
  assume "getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>1"
  moreover have "w (hd xs) \<le> real k \<longrightarrow> w (hd xs) \<le> real (Suc k)" for xs by simp
  ultimately show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v\<^sub>1))" 
    using a0 IH a1 Suc_leD by metis
next
  assume a3: "getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>2 + 1"
  then have "getL G w k v\<^sub>2 = a - 1" using a1 a3 le_diff_conv by auto
  then have "(\<exists> xs. decTrail G w xs \<and> length xs = a - 1 \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v\<^sub>2))" 
    using IH a0 Suc_leD by blast
  then obtain xs where f1: "decTrail G w xs \<and> length xs = a - 1 \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v\<^sub>2)" by blast
  moreover have "decTrail G w ((v\<^sub>1,v\<^sub>2)#xs)" 
  proof(rule disjE)
    show "length xs \<ge> 1 \<or> length xs = 0" by linarith
  next
    assume a3: "length xs = 0"
    have "w (v\<^sub>1,v\<^sub>2) = Suc k" using a0 a2 findEdge_surjective by fastforce
    then have "(v\<^sub>1,v\<^sub>2) \<in> parcs G" by (metis of_nat_neq_0 zero)
    then show "decTrail G w ((v\<^sub>1,v\<^sub>2)#xs)"
      using a3 using decTrail.simps(2) by blast
  next
    assume a3: "length xs \<ge> 1" 
    moreover have a4: "w (v\<^sub>1,v\<^sub>2) = Suc k" using a0 a2 findEdge_surjective  
      by (metis atLeastAtMost_iff fst_conv le_add1 plus_1_eq_Suc snd_conv)
    moreover have "w (v\<^sub>1,v\<^sub>2) > w (hd xs)"
      using a3 a4 f1 by linarith
    moreover have "(v\<^sub>1,v\<^sub>2) \<in> parcs G" 
      by (simp add: a4)
    moreover have "snd (v\<^sub>1,v\<^sub>2) = fst (hd xs)" using a3 f1 by auto
    ultimately show "decTrail G w ((v\<^sub>1,v\<^sub>2)#xs)" 
      using decTrail.elims(3) f1 by fastforce
  qed
  moreover have "length ((v\<^sub>1,v\<^sub>2)#xs) = a" 
    using f1 a1 a3 by force
  moreover have "w (hd ((v\<^sub>1,v\<^sub>2)#xs)) \<le> real (Suc k) \<and> fst (hd ((v\<^sub>1,v\<^sub>2)#xs)) = v\<^sub>1" 
    using a0 a2 distinct_weighted_pair_graph.findEdge_surjective(1) distinct_weighted_pair_graph_axioms by fastforce
  ultimately show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v\<^sub>1))" 
    by blast
qed

lemma aux_correctness_case_endpoint2:
  assumes a0: "(Suc k) \<le> q div 2"
      and a1: "getL G w (Suc k) v\<^sub>1 = a"
      and a2: "(findEdge w (set_to_list (parcs G)) (Suc k)) = (v\<^sub>2,v\<^sub>1)"
      and IH: "\<forall>a v. k \<le> q div 2 \<longrightarrow> getL G w k v = a \<longrightarrow> (\<exists> xs. decTrail G w xs \<and> length xs = a 
            \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v))" 
    shows "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v\<^sub>1))" 
proof(rule disjE)
  have "getL G w (Suc k) v\<^sub>1 = max (getL G w k v\<^sub>2 + 1) (getL G w k v\<^sub>1)"
    using a2 by auto
  then show "getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>2 + 1 \<or> getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>1" using a2 by linarith
next
  assume "getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>1"
  moreover have "w (hd xs) \<le> real k \<longrightarrow> w (hd xs) \<le> real (Suc k)" for xs by simp
  ultimately show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v\<^sub>1))" 
    using a0 IH a1 Suc_leD by metis
next
  assume a3: "getL G w (Suc k) v\<^sub>1 = getL G w k v\<^sub>2 + 1"
  then have "getL G w k v\<^sub>2 = a - 1" using a1 a3 le_diff_conv by auto
  then have "(\<exists> xs. decTrail G w xs \<and> length xs = a - 1 \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v\<^sub>2))" 
    using IH a0 Suc_leD by blast
  then obtain xs where f1: "decTrail G w xs \<and> length xs = a - 1 \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v\<^sub>2)" by blast
  moreover have "decTrail G w ((v\<^sub>1,v\<^sub>2)#xs)" 
  proof(rule disjE)
    show "length xs \<ge> 1 \<or> length xs = 0" by linarith
  next
    assume a3: "length xs = 0"
    have "w (v\<^sub>1,v\<^sub>2) = Suc k" using a0 a2 findEdge_surjective by fastforce
    then have "(v\<^sub>1,v\<^sub>2) \<in> parcs G" by (metis of_nat_neq_0 zero)
    then show "decTrail G w ((v\<^sub>1,v\<^sub>2)#xs)"
      using a3 using decTrail.simps(2) by blast
  next
    assume a3: "length xs \<ge> 1" 
    moreover have a4: "w (v\<^sub>1,v\<^sub>2) = Suc k" using a0 a2 findEdge_surjective  
      by (metis atLeastAtMost_iff fst_conv image_eqI le_add1 plus_1_eq_Suc snd_conv)
    moreover have "w (v\<^sub>1,v\<^sub>2) > w (hd xs)"
      using a3 a4 f1 by linarith
    moreover have "(v\<^sub>1,v\<^sub>2) \<in> parcs G" 
      by (simp add: a4)
    moreover have "snd (v\<^sub>1,v\<^sub>2) = fst (hd xs)" using a3 f1 by auto
    ultimately show "decTrail G w ((v\<^sub>1,v\<^sub>2)#xs)" 
      using decTrail.elims(3) f1 by fastforce
  qed
  moreover have "length ((v\<^sub>1,v\<^sub>2)#xs) = a" 
    using f1 a1 a3 by force
  moreover have "w (hd ((v\<^sub>1,v\<^sub>2)#xs)) \<le> real (Suc k) \<and> fst (hd ((v\<^sub>1,v\<^sub>2)#xs)) = v\<^sub>1" 
    using a0 a2 distinct_weighted_pair_graph.findEdge_surjective(1) distinct_weighted_pair_graph_axioms 
     atLeastAtMost_iff findEdge_surjective(2) by fastforce
  ultimately show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v\<^sub>1))" 
    by blast
qed

lemma aux_correctness:
  shows "\<forall>a v. k \<le> (q div 2) \<longrightarrow> getL G w k v = a \<longrightarrow> (\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v))" 
proof(induction k)
  show "\<forall>a v. 0 \<le> (q div 2) \<longrightarrow> getL G w 0 v = a \<longrightarrow> (\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real 0 \<and> fst (hd xs) = v))"
  proof (intro allI, intro impI)
    fix a v
    assume "0 \<le> (q div 2)" and "getL G w 0 v = a"
    then have "a = 0" by auto
    then have "decTrail G w [] \<and> length [] = a \<and> (length [] \<ge> 1 \<longrightarrow> w (hd []) \<le> real 0 \<and> fst (hd []) = v)"
      by auto
    then show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real 0 \<and> fst (hd xs) = v))" by blast
  qed
next
  fix k 
  assume IH: "\<forall>a v. k \<le> (q div 2) \<longrightarrow> getL G w k v = a \<longrightarrow> (\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real k \<and> fst (hd xs) = v))"
  show "\<forall>a v. (Suc k) \<le> (q div 2) \<longrightarrow> getL G w (Suc k) v = a \<longrightarrow> (\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v))"
  proof(rule allI, rule allI, rule impI, rule impI)
    fix a v
    assume a0: "(Suc k) \<le> (q div 2)"
    assume a1: "getL G w (Suc k) v = a"
    define v\<^sub>1 where "v\<^sub>1 = fst (findEdge w (set_to_list (arcs G)) (Suc k))"
    define v\<^sub>2 where "v\<^sub>2 = snd (findEdge w (set_to_list (arcs G)) (Suc k))"
    show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v))"
    proof(rule disjE)
      show "(v\<^sub>1 = v \<or> v\<^sub>2 = v) \<or> \<not>(v\<^sub>1 = v \<or> v\<^sub>2 = v)" by auto
    next
      assume "(v\<^sub>1 = v \<or> v\<^sub>2 = v)"
      then have "(\<exists> v\<^sub>2. (findEdge w (set_to_list (arcs G)) (Suc k)) = (v,v\<^sub>2)) 
               \<or> (\<exists> v\<^sub>2. (findEdge w (set_to_list (arcs G)) (Suc k)) = (v\<^sub>2,v))" 
        using v\<^sub>2_def v\<^sub>1_def by (simp add: prod_eq_iff)
      then show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v))"
        using aux_correctness_case_endpoint1 aux_correctness_case_endpoint2 a0 a1 IH v\<^sub>1_def v\<^sub>2_def by auto
    next
      assume "\<not>(v\<^sub>1 = v \<or> v\<^sub>2 = v)"
      then have "getL G w (Suc k) v = getL G w k v" 
        using v\<^sub>1_def v\<^sub>2_def getL.simps(2) by (smt old.prod.case prod.collapse)
      then show "(\<exists> xs. decTrail G w xs \<and> length xs = a \<and> (length xs \<ge> 1 \<longrightarrow> w (hd xs) \<le> real (Suc k) \<and> fst (hd xs) = v))"
        using IH Suc_leD a0 a1 le_SucI Suc_n_not_le_n of_nat_le_iff by fastforce
    qed
  qed
qed(*>*)
text \<open> Using an induction proof and extensive case distinction, the correctness of Algorithm \ref{algo} 
is then shown in our formalization, by proving the following theorem: \<close>

theorem(in distinct_weighted_pair_graph)  correctness:
  assumes "\<exists> v \<in> (pverts G). getL G w (q div 2) v = k"
  shows "\<exists> xs. decTrail G w xs \<and> length xs = k" 
(*<*)proof-
  have "(\<exists> xs. decTrail G w xs \<and> length xs = k)" 
    using assms aux_correctness by auto
  then obtain xs where f0: "decTrail G w xs \<and> length xs = k" by blast
  then have "length (drop (length xs - k) xs) = k" by simp
  moreover have "decTrail G w (drop (length xs - k) xs)" using incTrail_subtrail f0 decTrail_subtrail by blast
  ultimately show "\<exists> xs. decTrail G w xs \<and> length xs = k" by auto
qed(*>*)

subsection \<open> Minimum Length of Ordered Trails \<close>

(*<*)lemma aux_minimal_increase_one_step:
  shows "getL G w (i+1) (fst (findEdge w (set_to_list (arcs G)) (i+1)))
       + getL G w (i+1) (snd (findEdge w (set_to_list (arcs G)) (i+1)))
       \<ge> getL G w i (fst (findEdge w (set_to_list (arcs G)) (i+1))) + getL G w i (snd (findEdge w (set_to_list (arcs G)) (i+1))) + 2"
proof-
  define v where "v \<equiv> (findEdge w (set_to_list (arcs G)) (i+1))"
  define v\<^sub>1 where "v\<^sub>1 \<equiv> fst v"
  define v\<^sub>2 where "v\<^sub>2 \<equiv> snd v"
  have "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2  \<ge> getL G w i v\<^sub>1 + getL G w i v\<^sub>2 + 2"
  proof(rule disjE)
    show "(getL G w i v\<^sub>1 = getL G w i v\<^sub>2) \<or> (getL G w i v\<^sub>1 < getL G w i v\<^sub>2) \<or> (getL G w i v\<^sub>1 > getL G w i v\<^sub>2)" 
      by auto
  next
    assume a0: "(getL G w i v\<^sub>1 = getL G w i v\<^sub>2)"
    have "getL G w (i+1) v\<^sub>1 = (getL G w i v\<^sub>1) + 1" 
    proof-
      have "getL G w (i+1) v\<^sub>1 = max ((getL G w i v\<^sub>2)+1) (getL G w i v\<^sub>1)"
        using v\<^sub>1_def Suc_eq_plus1 getL.simps(2) v\<^sub>2_def v_def 
        by (smt old.prod.case prod.collapse)
      then show ?thesis
        using a0 by linarith
    qed
    moreover have "getL G w (i+1) v\<^sub>2 = (getL G w i v\<^sub>2) + 1" 
    proof-
      have "getL G w (i+1) v\<^sub>2 = max ((getL G w i v\<^sub>1)+1) (getL G w i v\<^sub>2)"
        using v\<^sub>1_def Suc_eq_plus1 getL.simps(2) v\<^sub>2_def v_def 
        by (smt old.prod.case prod.collapse)
      then show ?thesis using a0 by linarith
    qed
    ultimately show "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2  \<ge> getL G w i v\<^sub>1 + getL G w i v\<^sub>2 + 2"
      by simp
  next
    assume a0: "(getL G w i v\<^sub>1 < getL G w i v\<^sub>2) \<or> (getL G w i v\<^sub>1 > getL G w i v\<^sub>2)" 
    show "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2  \<ge> getL G w i v\<^sub>1 + getL G w i v\<^sub>2 + 2"
    proof(rule disjE) 
      show "(getL G w i v\<^sub>1 > getL G w i v\<^sub>2) \<or> (getL G w i v\<^sub>1 < getL G w i v\<^sub>2)" using a0 by blast
    next
      assume a1: "(getL G w i v\<^sub>1 < getL G w i v\<^sub>2)"
      then have "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2 = max ((getL G w i v\<^sub>2)+1) (getL G w i v\<^sub>1) + max ((getL G w i v\<^sub>1)+1) (getL G w i v\<^sub>2)"
        using v\<^sub>1_def v\<^sub>2_def Suc_eq_plus1 getL.simps(2) v_def 
        by (smt old.prod.case prod.collapse)
      then have "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2 = ((getL G w i v\<^sub>2)+1) + (getL G w i v\<^sub>2)"
        using a1 by linarith
      moreover have "getL G w i v\<^sub>1 + 1 \<le> getL G w i v\<^sub>2" using a1 by simp
      ultimately show "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2  \<ge> getL G w i v\<^sub>1 + getL G w i v\<^sub>2 + 2"
        by linarith
    next
      assume a1: "(getL G w i v\<^sub>1 > getL G w i v\<^sub>2)"
      then have "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2 = max ((getL G w i v\<^sub>2)+1) (getL G w i v\<^sub>1) + max ((getL G w i v\<^sub>1)+1) (getL G w i v\<^sub>2)"
        using v\<^sub>1_def v\<^sub>2_def using Suc_eq_plus1 getL.simps(2) v_def 
        by (smt old.prod.case prod.collapse)
      then have "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2 = ((getL G w i v\<^sub>1)+1) + (getL G w i v\<^sub>1)"
        using a1 by linarith
      moreover have "getL G w i v\<^sub>2 + 1 \<le> getL G w i v\<^sub>1" using a1 by simp
      ultimately show "getL G w (i+1) v\<^sub>1 + getL G w (i+1) v\<^sub>2  \<ge> getL G w i v\<^sub>1 + getL G w i v\<^sub>2 + 2"
        by linarith
    qed
  qed
  then show ?thesis using v\<^sub>2_def v\<^sub>1_def v_def by simp
qed(*>*)

text \<open>\label{minLength}
The algorithm introduced in Section \ref{compAlgo} is already useful on its own. Additionally, it can be
used to verify the lower bound on the minimum length of a strictly decreasing trail $P_d(w,G) \ge 2 \cdot \lfloor \frac{q}{n} \rfloor$.

To this end, Lemma 1 from Section \ref{PaperProof} is translated into Isabelle as the lemma
@{text "minimal_increase_one_step"}. The proof is 
similar to its counterpart, also using a case distinction. Lemma 2 is subsequently proved, here
named @{text "minimal_increase_total"}. \<close>

lemma(in distinct_weighted_pair_graph) minimal_increase_one_step:
  assumes "k + 1 \<in> W"
  shows 
    "(\<Sum> v \<in> pverts G. getL G w (k+1) v) \<ge> (\<Sum> v \<in> pverts G. getL G w k v) + 2" 

(*<*)proof-
  define u where "u \<equiv> (findEdge w (set_to_list (parcs G)) (k+1))" 
  define v\<^sub>1 where "v\<^sub>1 \<equiv> (fst u)" 
  define v\<^sub>2 where "v\<^sub>2 \<equiv> (snd u)" 
  have f0: "v\<^sub>1 \<in> (pverts G)" using findEdge_bound assms 
    by (metis (full_types) Suc_eq_plus1 distinct_weighted_pair_graph.findEdge_surjective(2) 
distinct_weighted_pair_graph_axioms of_nat_neq_0 u_def v\<^sub>1_def weight_zero)
  have f1: "v\<^sub>2 \<in> (pverts G)" 
    using findEdge_bound assms 
    by (metis (full_types) Suc_eq_plus1 findEdge_surjective(2) of_nat_0_neq u_def v\<^sub>1_def v\<^sub>2_def weight_zero)
  have f2: "finite (pverts G)" by simp
  have "v\<^sub>1 \<in> pverts G" by (simp add: f0)
  have f3: "v\<^sub>1 \<noteq> v\<^sub>2" using u_def v\<^sub>1_def v\<^sub>2_def 
    by (metis (mono_tags, lifting) Suc_eq_plus1 assms distinct_weighted_pair_graph.findEdge_surjective(2) distinct_weighted_pair_graph_axioms of_nat_0_eq_iff pair_no_loops prod.collapse weight_not_zero_implies_arc zero_eq_add_iff_both_eq_0 zero_neq_one)
  then have "(\<Sum> v \<in> pverts G. getL G w (k+1) v) = (\<Sum> v \<in> (pverts G). getL G w (k+1) v)" by blast
  also have "... = (\<Sum> v \<in> (pverts G) - {v\<^sub>1}. getL G w (k+1) v) + getL G w (k+1) v\<^sub>1" 
    using f0 f2 sum.remove by (metis add.commute)
  also have "... = (\<Sum> v \<in> (pverts G) - {v\<^sub>1,v\<^sub>2}. getL G w (k+1) v) + getL G w (k+1) v\<^sub>2 + getL G w (k+1) v\<^sub>1" 
    by (smt Diff_insert add.commute add.left_commute f0 f1 f2 f3 finite_Diff insertE insert_Diff sum.remove)
  also have "... \<ge> (\<Sum> v \<in> (pverts G) - {v\<^sub>1,v\<^sub>2}. getL G w (k+1) v) + getL G w k v\<^sub>2 + getL G w k v\<^sub>1 + 2" 
    using aux_minimal_increase_one_step u_def v\<^sub>1_def v\<^sub>2_def 
    by (smt add.assoc add.commute le_add2 le_trans nat_add_left_cancel_le with_proj_simps(2))
  finally have "(\<Sum> v \<in> pverts G. getL G w (k+1) v) \<ge> (\<Sum> v \<in> (pverts G) - {v\<^sub>1,v\<^sub>2}. getL G w (k+1) v) + 2" 
    using \<open>sum (getL G w (k + 1)) ((pverts G) - {v\<^sub>1, v\<^sub>2}) + getL G w k v\<^sub>2 + getL G w k v\<^sub>1 + 2 \<le> sum (getL G w (k + 1)) ((pverts G) - {v\<^sub>1, v\<^sub>2}) + getL G w (k + 1) v\<^sub>2 + getL G w (k + 1) v\<^sub>1\<close> 
\<open>sum (getL G w (k + 1)) ((pverts G) - {v\<^sub>1}) + getL G w (k + 1) v\<^sub>1 = sum (getL G w (k + 1)) ((pverts G) - {v\<^sub>1, v\<^sub>2}) + getL G w (k + 1) v\<^sub>2 + getL G w (k + 1) v\<^sub>1\<close> \<open>sum (getL G w (k + 1)) (pverts G) = sum (getL G w (k + 1)) ((pverts G) - {v\<^sub>1}) + getL G w (k + 1) v\<^sub>1\<close> by linarith
  moreover have "\<forall>v \<in> (pverts G) - {v\<^sub>1,v\<^sub>2}. getL G w (k+1) v = getL G w k v"
    using aux_getL u_def v\<^sub>1_def v\<^sub>2_def by auto
  ultimately have "(\<Sum> v \<in> pverts G. getL G w (k+1) v) \<ge> (\<Sum> v \<in> (pverts G) - {v\<^sub>1,v\<^sub>2}. getL G w k v) + getL G w k v\<^sub>2 + getL G w k v\<^sub>1 + 2" 
    using \<open>sum (getL G w (k + 1)) (pverts G - {v\<^sub>1, v\<^sub>2}) + getL G w k v\<^sub>2 + getL G w k v\<^sub>1 + 2 \<le> sum (getL G w (k + 1)) (pverts G - {v\<^sub>1, v\<^sub>2}) + getL G w (k + 1) v\<^sub>2 + getL G w (k + 1) v\<^sub>1\<close> 
\<open>sum (getL G w (k + 1)) (pverts G - {v\<^sub>1}) + getL G w (k + 1) v\<^sub>1 = sum (getL G w (k + 1)) (pverts G - {v\<^sub>1, v\<^sub>2}) + getL G w (k + 1) v\<^sub>2 + getL G w (k + 1) v\<^sub>1\<close> 
\<open>sum (getL G w (k + 1)) (pverts G) = sum (getL G w (k + 1)) (pverts G - {v\<^sub>1}) + getL G w (k + 1) v\<^sub>1\<close> by auto
  then have "(\<Sum> v \<in> pverts G. getL G w (k+1) v) \<ge> (\<Sum> v \<in> (pverts G). getL G w k v) + 2" 
    using Diff_idemp Diff_insert2 Diff_insert_absorb Nat.le_diff_conv add.commute add_leD2 
add_le_imp_le_diff f1 f2 finite_Diff insert_Diff sum.insert_remove 
    by (smt Nat.le_diff_conv2)
  then show ?thesis by blast
qed

lemma aux_minimal_increase_total:
  assumes "i \<ge> 1"
  shows "i \<in> W \<longrightarrow> (\<Sum> v \<in> pverts G. getL G w i v) \<ge> 2*i"
proof(rule Nat.nat_induct_at_least[of 1 i])
  show "i \<ge> 1" using assms by simp
next
  show "1 \<in> W \<longrightarrow> (\<Sum> v \<in> pverts G. getL G w 1 v) \<ge> 2*1"
    using minimal_increase_one_step[of 0] by auto
next
  fix i::nat
  assume a0: "i \<ge> 1"
  assume IH: "i \<in> W \<longrightarrow> (\<Sum> v \<in> pverts G. getL G w i v) \<ge> 2*i"
  show "Suc i \<in> W \<longrightarrow> (\<Sum> v \<in> pverts G. getL G w (Suc i) v) \<ge> 2*(Suc i)"
  proof
    assume a1: "Suc i \<in> W"
    then have "(\<Sum> v \<in> pverts G. getL G w (Suc i) v) \<ge> (\<Sum> v \<in> pverts G. getL G w i v) + 2"
      using minimal_increase_one_step Suc_eq_plus1 by metis
    moreover have "i \<in> W" using a0 a1 by auto
    ultimately have "(\<Sum> v \<in> pverts G. getL G w (Suc i) v) \<ge> 2*i + 2" using IH by auto
    then show "(\<Sum> v \<in> pverts G. getL G w (Suc i) v) \<ge> 2*(Suc i)" by auto
  qed
qed(*>*)


lemma(in distinct_weighted_pair_graph) minimal_increase_total:
  shows "(\<Sum> v \<in> pverts G. getL G w (q div 2) v) \<ge> q"
(*<*)proof(cases)
  assume "q = 0"
  then show "(\<Sum> v \<in> pverts G. getL G w (q div 2) v) \<ge> q" by simp
next
  assume "q \<noteq> 0" 
  then have "1 \<le> q div 2" using even_arcs by fastforce
  moreover have "q div 2 \<in> W" using atLeastAtMost_iff calculation by blast
  moreover have "2*(q div 2) = q" 
    using dvd_mult_div_cancel even_arcs by blast
  ultimately show ?thesis using aux_minimal_increase_total[of "q div 2"] by auto
qed(*>*)

(*<*)lemma set_sum: 
  assumes "k \<ge> 1" and "card A = k" and "(\<forall> v \<in> A. f v < (q div n) \<and> f v \<ge> 0)"
  shows "(\<Sum> v \<in> A. f v) < (q div n)*k" 
proof(rule disjE)
  show "k = 1 \<or> k \<ge> 2" using assms by auto
next
  assume "k = 1" 
  then show "(\<Sum> v \<in> A. f v) < (q div n)*k" using assms sum_bounded_above_strict by fastforce
next
  assume "k \<ge> 2"
  then have "(\<Sum> v \<in> A. f v) < (\<Sum>i\<in>A. (q div n))" 
    using sum_mono[of A f "\<lambda>i. k-1"] assms 
    by (metis Suc_1 card.empty card_infinite le_less nat.simps(3) not_numeral_less_zero sum_strict_mono)
  moreover have "(\<Sum>i\<in>A. (q div n)) = k*(q div n)" using assms(2) by auto
  ultimately show ?thesis 
    by (metis mult.commute)
qed(*>*)

text \<open> From @{term "minimal_increase_total"} we have that that the sum of all labels after $q$ div $2$ steps is 
greater than $q$. Now assume that all labels are smaller than $q$ div $n$. Because we have $n$ vertices, this
leads to a contradiction, which proves @{text "algo_result_min"}. \<close>

lemma(in distinct_weighted_pair_graph) algo_result_min: 
  shows "(\<exists> v \<in> pverts G. getL G w (q div 2) v \<ge> q div n)"
(*<*)proof(rule ccontr)
  assume "\<not> (\<exists> v \<in> pverts G. getL G w (q div 2) v \<ge> q div n)" 
  then have "(\<forall> v \<in> pverts G. getL G w (q div 2) v < q div n)" by auto
  then have "(\<Sum> v \<in> pverts G. getL G w (q div 2) v) < q div n*n" using set_sum[of n "(pverts G)" "\<lambda>v. getL G w (q div 2) v"] vert_ge by auto 
  then have "(\<Sum> v \<in> pverts G. getL G w (q div 2) v) < q" 
    by (metis Groups.add_ac(2) add_mono_thms_linordered_field(4) div_times_less_eq_dividend nat_add_left_cancel_less)
  moreover have "(\<Sum> v \<in> pverts G. getL G w (q div 2) v) \<ge> q" 
    by (simp add: minimal_increase_total)
  ultimately show False by auto
qed(*>*)

text \<open> Finally, using lemma @{term "algo_result_min"} together with the @{term "correctness"} theorem 
of section \ref{compAlgo}, we prove the lower bound of $2\cdot\lfloor \frac{q}{n} \rfloor$ over the length 
of a longest strictly decreasing trail. This general approach could also be used to extend our
formalization and prove existence of other trails. For example, assume that some restrictions on the graph 
give raise to the existence of a trail of length $m \ge 2\cdot\lfloor \frac{q}{n} \rfloor$. Then, it is
only necessary to show that our algorithm can find this trail. \<close>

theorem(in distinct_weighted_pair_graph) dec_trail_exists: 
  shows "\<exists> es. decTrail G w es \<and> length es = q div n" 
(*<*)proof-
  have "\<exists>v. \<exists>xs. decTrail G w xs \<and> length xs = getL G w (q div 2) v" 
    using algo_result_min correctness by blast
  then have "(\<exists> xs. decTrail G w xs \<and> length xs \<ge> q div n)" 
    using algo_result_min by (metis correctness)
  then obtain xs where "decTrail G w xs \<and> length xs \<ge> q div n" by blast
  moreover have "length (drop (length xs - q div n) xs) = q div n" by (simp add: calculation)
  ultimately show "(\<exists> xs. decTrail G w xs \<and> length xs = q div n)" 
    using decTrail_subtrail by blast
qed(*>*)


theorem(in distinct_weighted_pair_graph) inc_trail_exists: 
  shows "\<exists> es. incTrail G w es \<and> length es = q div n"
  (*<*)using dec_trail_exists 
  by (smt distinct graph_symmetric in_arcsD1 length_map length_rev pair_sym_digraph.decTrail_eq_rev_incTrail pair_sym_digraph_axioms undirected zero)
(*>*)
text \<open> Corollary 1 is translated into @{text "dec_trail_exists_complete"}. The proof first argues
that the number of edges is $n\cdot(n-1)$ by restricting its domain as done already in Section \ref{localeSurjective}.
  \<close>

lemma(in distinct_weighted_pair_graph) dec_trail_exists_complete: 
  assumes "complete_digraph n G" 
  shows "(\<exists> es. decTrail G w es \<and> length es = n-1)" 
(*<*)proof-
  have "card (arcs G) = (n * (n-1))" 
  proof-
    have "arcs G = {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2}" using assms complete_digraph_pair_def by auto
    moreover have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} = n*(n-1)"  (*TODO: Same code as above, make own lemma *)
  proof-
    have "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} = {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
    proof
      show "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} \<subseteq> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
      proof
        fix x 
        assume a0: "x \<in> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2}"
        then have "x \<in> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G}" by blast
        moreover have "x \<notin> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}" using a0 by blast
        ultimately show "x \<in> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
          by blast
      qed
    next
      show "{v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}
                \<subseteq> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2}"
        by blast
    qed
    moreover have "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} \<subseteq> {v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G}" by blast
    moreover have "finite {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}" 
      using calculation(2) finite_subset by fastforce
    ultimately have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} 
                   = card ({v\<^sub>1. v\<^sub>1 \<in> pverts G} \<times> {v\<^sub>2. v\<^sub>2 \<in> pverts G}) - card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}"
      by (simp add: card_Diff_subset)
    moreover have "card {v\<^sub>1. v\<^sub>1 \<in> pverts G} = n" by auto
    moreover have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} = card {v\<^sub>1. v\<^sub>1 \<in> pverts G}" 
    proof-
      have "inj_on (\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2}" 
        by (smt Product_Type.Collect_case_prodD inj_onI prod.case_eq_if prod.collapse)
      moreover have "(\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) ` {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} = {v\<^sub>1. v\<^sub>1 \<in> pverts G}" by auto
      ultimately have "bij_betw (\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 = v\<^sub>2} {v\<^sub>1. v\<^sub>1 \<in> pverts G}" 
        by (simp add: bij_betw_def)
      then show ?thesis 
        using bij_betw_same_card by auto
    qed
    ultimately have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> pverts G \<and> v\<^sub>2 \<in> pverts G \<and> v\<^sub>1 \<noteq> v\<^sub>2} = n*n - n" by auto
    then show ?thesis 
      by (simp add: diff_mult_distrib2)
  qed
  ultimately show ?thesis by simp
qed
  then show ?thesis 
    using dec_trail_exists by auto 
qed

end (* context graph *)

lemma aux_complete_graph_edges:
  assumes "finite A" 
  shows "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2} = (card A)*(card A-1)"  (*TODO: Same code as above, make own lemma *)
  proof-
    have "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2} = {v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}"
    proof
      show "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2} \<subseteq> {v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}"
      proof
        fix x 
        assume a0: "x \<in> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2}"
        then have "x \<in> {v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A}" by blast
        moreover have "x \<notin> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}" using a0 by blast
        ultimately show "x \<in> {v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}"
          by blast
      qed
    next
      show "{v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A} - {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}
                \<subseteq> {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2}"
        by blast
    qed
    moreover have "{(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2} \<subseteq> {v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A}" by blast
    moreover have "finite {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}" 
      using calculation(2) finite_subset assms by auto
    ultimately have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2} 
                   = card ({v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A}) - card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}"
      by (simp add: card_Diff_subset)
    moreover have "card {v\<^sub>1. v\<^sub>1 \<in> A} = (card A)" by auto
    moreover have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2} = card {v\<^sub>1. v\<^sub>1 \<in> A}" 
    proof-
      have "inj_on (\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}" 
        by (smt Product_Type.Collect_case_prodD inj_onI prod.case_eq_if prod.collapse)
      moreover have "(\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) ` {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2} = {v\<^sub>1. v\<^sub>1 \<in> A}" by auto
      ultimately have "bij_betw (\<lambda>(v\<^sub>1,v\<^sub>2). v\<^sub>1) {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2} {v\<^sub>1. v\<^sub>1 \<in> A}" 
        by (simp add: bij_betw_def)
      then show ?thesis 
        using bij_betw_same_card by auto
    qed
    ultimately have "card {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2} = (card A)*(card A) - (card A)" 
      by (simp add: \<open>card {(v\<^sub>1, v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 \<noteq> v\<^sub>2} = card ({v\<^sub>1. v\<^sub>1 \<in> A} \<times> {v\<^sub>2. v\<^sub>2 \<in> A}) - card {(v\<^sub>1, v\<^sub>2). v\<^sub>1 \<in> A \<and> v\<^sub>2 \<in> A \<and> v\<^sub>1 = v\<^sub>2}\<close> card_cartesian_product)
    then show ?thesis 
      by (simp add: diff_mult_distrib2)
  qed
(*>*)

subsection \<open> Example Graph $K_4$ \<close>

text \<open> We return to the example graph from Figure \ref{exampleGraph} and show that our results from 
Sections \ref{trails}-\ref{minLength} can be used to prove existence of trails of length $k$, in particular
$k = 3$ in $K_4$. Defining the graph and the 
weight function separately, we use natural numbers as vertices. \<close>

abbreviation ExampleGraph:: "nat pair_pre_digraph" where 
"ExampleGraph \<equiv> (| 
pverts = {1,2,3,(4::nat)}, 
parcs = {(v\<^sub>1,v\<^sub>2). v\<^sub>1 \<in> {1,2,3,(4::nat)} \<and> v\<^sub>2 \<in> {1,2,3,(4::nat)} \<and> v\<^sub>1 \<noteq> v\<^sub>2} 
|)" 

abbreviation ExampleGraphWeightFunction :: "(nat\<times>nat) weight_fun" where 
"ExampleGraphWeightFunction \<equiv> (\<lambda>(v\<^sub>1,v\<^sub>2). 
                               if (v\<^sub>1 = 1 \<and> v\<^sub>2 = 2) \<or> (v\<^sub>1 = 2 \<and> v\<^sub>2 = 1) then 1 else
                              (if (v\<^sub>1 = 1 \<and> v\<^sub>2 = 3) \<or> (v\<^sub>1 = 3 \<and> v\<^sub>2 = 1) then 3 else
                              (if (v\<^sub>1 = 1 \<and> v\<^sub>2 = 4) \<or> (v\<^sub>1 = 4 \<and> v\<^sub>2 = 1) then 6 else
                              (if (v\<^sub>1 = 2 \<and> v\<^sub>2 = 3) \<or> (v\<^sub>1 = 3 \<and> v\<^sub>2 = 2) then 5 else 
                              (if (v\<^sub>1 = 2 \<and> v\<^sub>2 = 4) \<or> (v\<^sub>1 = 4 \<and> v\<^sub>2 = 2) then 4 else
                              (if (v\<^sub>1 = 3 \<and> v\<^sub>2 = 4) \<or> (v\<^sub>1 = 4 \<and> v\<^sub>2 = 3) then 2 else 
                               0))))))" 

(*<*) (*TODO: Lemma name convention *)
lemma codomain_ExampleGraphWeightFunction:
  assumes "(x,y) \<in> parcs ExampleGraph"
  shows "ExampleGraphWeightFunction (x,y) \<in> {1,2,3,4,5,6}" 
proof-
  have "{(v::nat,w::nat). v \<in> {1,2,3,(4::nat)} \<and> w \<in> {1,2,3,(4::nat)} \<and> v \<noteq> w} = {(1,2),(2,1),(3,1),(1,3),(1,4),(4,1),(2,3),(3,2),(2,4),(4,2),(3,4),(4,3)}"
    by auto
  then have "(x,y) \<in> {(1,2),(2,1),(3,1),(1,3),(1,4),(4,1),(2,3),(3,2),(2,4),(4,2),(3,4),(4,3)}" 
    using assms by auto
  then show ?thesis 
    using singletonD by auto
qed

lemma zero_ExampleGraphWeightFunction:
  assumes "(x,y) \<notin> parcs ExampleGraph"
  shows "ExampleGraphWeightFunction (x,y) = 0" 
proof-
  have "{(v::nat,w::nat). v \<in> {1,2,3,(4::nat)} \<and> w \<in> {1,2,3,(4::nat)} \<and> v \<noteq> w} = {(1,2),(2,1),(3,1),(1,3),(1,4),(4,1),(2,3),(3,2),(2,4),(4,2),(3,4),(4,3)}"
    by auto
  then have "(x,y) \<notin> {(1,2),(2,1),(3,1),(1,3),(1,4),(4,1),(2,3),(3,2),(2,4),(4,2),(3,4),(4,3)}" 
    using assms by auto
  then show ?thesis 
    using singletonD by auto
qed

lemma card_parcs_ExampleGraph:
  shows "card (parcs ExampleGraph) = 12" 
proof-
  have "finite {1,2,3,4}" by blast 
  moreover have "card {1,2,3,(4::nat)} = 4" by simp
  ultimately show "card (parcs ExampleGraph) = 12" 
    using aux_complete_graph_edges[of "{1,2,3,(4::nat)}"] by force
qed(*>*)
text \<open> We show that the graph $K_4$ of Figure \ref{exampleGraph} satisfies the conditions that were
imposed in 
@{text "distinct_weighted_pair_graph"} and its parent locale, including for example no self loops 
and distinctiveness. Of course there is still some effort required for this. However, it is necessary
to manually construct trails or list all possible weight distributions. Additionally, instead of 
$q!$ statements there are at most $\frac{3q}{2}$ statements needed.  \<close>

interpretation example: 
  distinct_weighted_pair_graph ExampleGraph ExampleGraphWeightFunction
(*<*)proof
  show f0: "\<And>e. e \<in> parcs ExampleGraph \<Longrightarrow> fst e \<in> pverts ExampleGraph" by auto
  show f1: "\<And>e. e \<in> parcs ExampleGraph \<Longrightarrow> snd e \<in> pverts ExampleGraph" by auto
  show "finite (pverts ExampleGraph)" by simp
  show "finite (parcs ExampleGraph)" 
  proof-
    have "finite {1,2,3,4}" by blast 
    moreover have "card {1,2,3,(4::nat)} = 4" by simp
    ultimately have "card (parcs ExampleGraph) = 12" 
      using aux_complete_graph_edges[of "{1,2,3,(4::nat)}"] by force
    then show ?thesis using card_ge_0_finite[of "parcs ExampleGraph"] by auto
  qed
  show "\<And>e. e \<in> parcs ExampleGraph \<Longrightarrow> fst e \<noteq> snd e" by auto
  show "symmetric (with_proj ExampleGraph)" 
    by (metis (mono_tags, lifting) f0 f1 case_prodI mem_Collect_eq pair_pre_digraph.select_convs(1) 
        pair_pre_digraph.select_convs(2) prod.sel(1) prod.sel(2) symI symmetric_def with_proj_simps(3)) 
  show "\<And>x::nat \<times> nat. x \<in> parcs ExampleGraph \<longrightarrow> ExampleGraphWeightFunction x \<in> real ` {1::nat..card (parcs ExampleGraph) div (2::nat)}" 
  proof
    fix x
    assume a0: "x \<in> parcs ExampleGraph"
    have "finite {1,2,3,4}" by blast 
    moreover have "card {1,2,3,(4::nat)} = 4" by simp
    ultimately have "card (parcs ExampleGraph) = 12" 
      using aux_complete_graph_edges[of "{1,2,3,(4::nat)}"] by force
    then have f0: "card (parcs ExampleGraph) div 2 = 6" by auto 
    moreover have "real ` {1..card (parcs ExampleGraph) div 2} = {1,2,3,4,5,(6::real)}" 
    proof-
      have "real ` {1..card (parcs ExampleGraph) div 2} = real ` {1..(6::nat)}" using f0 by auto
      moreover have "{1..(6::nat)} = {1,2,3,4,5,6}" by auto
      ultimately have "real ` {1..card (parcs ExampleGraph) div 2} = real ` {1,2,3,4,5,(6::nat)}" by auto
      then show "real ` {1..card (parcs ExampleGraph) div 2} = {1,2,3,4,5,(6::real)}" by auto
    qed
    ultimately show "ExampleGraphWeightFunction x \<in> real ` {1::nat..card (parcs ExampleGraph) div (2::nat)}" 
      using codomain_ExampleGraphWeightFunction 
      by (metis (no_types, lifting) a0 prod.collapse)
  qed
  show "1 \<le> card (pverts ExampleGraph)" by simp
  show "\<forall>x y. ((x, y) \<notin> parcs ExampleGraph) = (ExampleGraphWeightFunction (x, y) = 0)" 
    by (smt \<open>\<And>x::nat \<times> nat. x \<in> parcs ExampleGraph \<longrightarrow> ExampleGraphWeightFunction x \<in> real ` {1::nat..card (parcs ExampleGraph) div (2::nat)}\<close> atLeastAtMost_iff imageE le_numeral_extra(2) of_nat_0_eq_iff zero_ExampleGraphWeightFunction)
  show "\<forall>(x, y)\<in>parcs ExampleGraph.
        \<forall>(z, a)\<in>parcs ExampleGraph. (x = a \<and> y = z \<or> x = z \<and> y = a) = (ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a))" 
  proof-
    have "\<forall>x y z a. (x,y) \<in> parcs ExampleGraph \<and> (z, a) \<in> parcs ExampleGraph \<longrightarrow>  (x = a \<and> y = z \<or> x = z \<and> y = a) = (ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a))" 
    proof (intro allI, rule impI)
      fix x y z a
      assume a0: "(x,y) \<in> parcs ExampleGraph \<and> (z, a) \<in> parcs ExampleGraph "
      have "(x = a \<and> y = z \<or> x = z \<and> y = a) \<longrightarrow> (ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a))" 
      proof-
        have "x = a \<and> y = z \<longrightarrow> (ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a))"
        proof-
          have "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4" and "y = 1 \<or> y = 2 \<or> y = 3 \<or> y = 4" and "x \<noteq> y"
            using a0 by auto
          moreover have "ExampleGraphWeightFunction (1, 2) = ExampleGraphWeightFunction (2, 1)" by auto
          moreover have "ExampleGraphWeightFunction (1, 3) = ExampleGraphWeightFunction (3, 1)" by auto
          moreover have "ExampleGraphWeightFunction (1, 4) = ExampleGraphWeightFunction (4, 1)" by auto
          moreover have "ExampleGraphWeightFunction (2, 3) = ExampleGraphWeightFunction (3, 2)" by auto
          moreover have "ExampleGraphWeightFunction (2, 4) = ExampleGraphWeightFunction (4, 2)" by auto
          moreover have "ExampleGraphWeightFunction (3, 4) = ExampleGraphWeightFunction (4, 3)" by auto
          ultimately have "(ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (y, x))" by presburger
          then show ?thesis by blast
        qed          
        moreover have "x = z \<and> y = a \<longrightarrow> (ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a))"
        by blast
        ultimately show ?thesis by blast
    qed      
    moreover have "(ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a)) \<longrightarrow> (x = a \<and> y = z \<or> x = z \<and> y = a)" 
    proof-
      have "ExampleGraphWeightFunction (x, y) = 0 \<and> ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a) 
              \<longrightarrow> x = a \<and> y = z \<or> x = z \<and> y = a" using a0 f1 by auto
      moreover have "ExampleGraphWeightFunction (x, y) = 1 \<and> ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a) 
              \<longrightarrow> x = a \<and> y = z \<or> x = z \<and> y = a" by auto
      moreover have "ExampleGraphWeightFunction (x, y) = 2 \<and> ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a) 
              \<longrightarrow> x = a \<and> y = z \<or> x = z \<and> y = a" by auto
      moreover have "ExampleGraphWeightFunction (x, y) = 3 \<and> ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a) 
              \<longrightarrow> x = a \<and> y = z \<or> x = z \<and> y = a" by auto
      moreover have "ExampleGraphWeightFunction (x, y) = 4 \<and> ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a) 
              \<longrightarrow> x = a \<and> y = z \<or> x = z \<and> y = a" by auto
      moreover have "ExampleGraphWeightFunction (x, y) = 5 \<and> ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a) 
              \<longrightarrow> x = a \<and> y = z \<or> x = z \<and> y = a" by auto
      moreover have "ExampleGraphWeightFunction (x, y) = 6 \<and> ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a) 
              \<longrightarrow> x = a \<and> y = z \<or> x = z \<and> y = a" by auto
      moreover have "ExampleGraphWeightFunction (x, y) = 0 \<or> ExampleGraphWeightFunction (x, y) = 1 \<or>
          ExampleGraphWeightFunction (x, y) = 2 \<or> ExampleGraphWeightFunction (x, y) = 3 \<or> 
          ExampleGraphWeightFunction (x, y) = 4 \<or> ExampleGraphWeightFunction (x, y) = 5 \<or> 
          ExampleGraphWeightFunction (x, y) = 6" 
        by auto
      ultimately show "(ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a)) \<longrightarrow> (x = a \<and> y = z \<or> x = z \<and> y = a)" 
        by smt
    qed
    ultimately show "(x = a \<and> y = z \<or> x = z \<and> y = a) = (ExampleGraphWeightFunction (x, y) = ExampleGraphWeightFunction (z, a))" by blast
    qed
    then show ?thesis by blast
  qed
qed
(*>*)

text \<open> Now it is an easy task to prove that there is a trail of length 3. We only add the fact that
@{text ExampleGraph} is a @{text "distinct_weighted_pair_graph"} and lemma @{text "dec_trail_exists"}.\<close>

lemma ExampleGraph_decTrail:
  "\<exists> xs. decTrail ExampleGraph ExampleGraphWeightFunction xs \<and> length xs = 3"
(*<*)  using example.distinct_weighted_pair_graph_axioms example.dec_trail_exists card_parcs_ExampleGraph 
    card_parcs_ExampleGraph by auto (*>*)

section \<open> Discussion and Related Work \<close>

text \<open>
Our formalization can be easily extended and could therefore serve as a basis for further work in this field.
The definitions @{term "incTrail"} and @{term "decTrail"} and the respective properties that are proven in 
Section \ref{trails} are the key to many other variants of trail properties. 

Graham et al.~\cite{graham1973increasing} also showed upper bounds for trails in complete graphs by decomposing
them into either into cycles or 1-factors. We are currently working on formalizing and certifying the result 
that 

$$
f_d(n)= f_i(n) = 
\begin{cases}
n &  \text{if } n \in \{3,5\}\\
n-1 & \text{otherwise}\\
\end{cases},
$$

that is for complete graphs with $n=3$ or $n=5$ vertices there always has to be a trail of length at least $n$ whereas 
for any other number $n$ of vertices there only has to be a trail of length $n - 1$. Therefore, the lower bound that
we showed in this paper is equal to the exact length with exception of two special cases.  
We believe that formalizing this result would be a valuable extension to the theory @{text "Ordered_Trail"}.

Another direction for further investigation are monotone paths. 
Graham et al. \cite{graham1973increasing} show that in a complete graph with $n$ vertices there has to be an increasing path of length 
at least $\frac{1}{2}(\sqrt{4n-3}-1)$ and at most $\frac{3n}{4}$. 
The upper bound was afterwards improved by Calderbank, Chung and Sturtevant \cite{calderbank1984increasing}, 
Milans \cite{milans2015monotone} and Buci{\'c} et al. \cite{bucic2018nearly}. 

Recently, other classes of graphs have been considered, e.g., trees and planar graphs \cite{roditty2001monotone},
on random edge-ordering \cite{yuster2001large} or on hypercubes \cite{de2015increasing}.\<close>

section "Conclusion"

text \<open>
In this work we formalized strictly increasing and strictly decreasing trails in the proof assistant Isabelle/HOL. 
Furthermore, we showed correctness of an algorithm to find such trails. We provided a verified algorithm and program to compute monotone trails. 
We used this algorithm to
prove the result that every graph with $n$ vertices and $q$ edges has a strictly decreasing trail of length at least
$2\cdot\lfloor\frac{q}{n}\rfloor$. For further work we plan to show that this is a tight bound for every $n$ except for $n = 3$ and $5$. 

Our results are built on the already existing Isabelle @{text "Graph_theory"} from the Archive of Formal Proofs. 
Thus, our results can be used by any theory using graphs that are specified as in this library.
Therefore, our theory is highly reusable and might be the basis for further work in this field.\<close>

(*<*)end(*>*)