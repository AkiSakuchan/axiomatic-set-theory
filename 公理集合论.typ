#import "book-style.typ": *
#import "@preview/theorion:0.3.3": *
#import "@preview/commute:0.3.0": node, arr, commutative-diagram
#import cosmos.rainbow: *
#show: show-theorion

#let vdash = math.class("normal", math.tack.r)
#let Vdash = math.class("normal", math.tack.r.double)

= ZFC 集合论
现在我们可以谈论 ZFC 公理集合论了。
- ZFC 集合论是一种带等号的一阶理论（参见 @等号公理）。
- 它的变量我们除了 $x_1,x_2,x_3,dots$ 来表示外，也用 $x,y,z$ 等最后的字母以及它们带下标的形式来表示，有时为了区分也用大写字母。
- 它没有常量。
- 它的谓词除了等号以外还有一个二元谓词 $A_2^2$，用 $a in b$ 表示 $A_2^2(a,b)$，用 $a in.not b$ 表示 $not A_2^2(a,b)$。
直觉上 $a in b$ 表示 $a$ 是 $b$ 的元素。另外我们还要定义包含符号：

#nonum-equation[$a subset.eq b := (forall x)(x in a -> x in b)$]

== 公理

#axiom(title: "外延公里")[
  #nonum-equation($(forall x)(forall y)[ (forall z)(z in x <-> z in y)] -> x = y$)

  这条公理直觉上就是两个集合如果它们的元素属于关系完全等价，则这两个类就相等。
]<外延公里>
上述从 $x = y$ 反过来得到那个公式可以直接从等号的替换性得到。

#axiom(title: "正规公理")[
  #nonum-equation($
      (forall x)lr({(exists a)(a in x) -> (exists y) lr({ (y in x) and not lr({(exists z) (z in y and z in x)}, size: #(1.5em)) }, size: #(2em)) }, size:#(3em))
  $)
  翻译成人话就是非空集合 $x$ （第一个 $exists$ 只表示 $x$ 非空）里存在一个元素 $y$，它和 $x$ 不相交。
]<正规公理>

#axiom(title: "替换公理")[
  这是个公理模式。设 $cal(P)$ 是二元谓词公式。则替换公理是
  #nonum-equation[
    $ (forall x)(exists ! y) cal(P)(x,y) -> 
    (forall A) (exists B) lr([y in B <-> (exists x)(x in A and cal(P)(x,y))], size: #(1.2em)) $
  ]
  这里 $exists!$ 表示唯一存在，它可以用 $exists$ 结合全称量词和等号来定义。
  这条公理用人话说就是如果对任意 $x$，都存在唯一 $y$ 使得性质 $cal(P)(x,y)$ 成立，
  那么对任意集合 $A$，都存在集合 $B$ 使得 $y in B$ 当且仅当有 $x in A$ 使得 $cal(P)(x,y)$。
]<替换公理>
首先满足条件的 $cal(P)(x,y)$ 实际上可以定义一个"函数" $F$，把 $F(x) = y$ 定义为 $cal(P)(x,y)$，后半部分实际上要求对任意集合
$A$，都有集合 $B$ 使得 $B$ 中的元素都是 $A$ 中元素经过 $F$ 作用得来。

#axiom(title: "分类公理")[
  设 $cal(P)$ 是一元谓词公式，且设 $B$ 是 $cal(P)$ 的自由变量。那么
  #nonum-equation[
    $ (forall A)(exists B)lr(size: #(1.3em) ,[(forall x)(x in B <-> x in A and cal(P)(x) ) ] )  $
  ]
  用人话说就是对任意集合 $A$ 都存在集合 $B$ 使得 $B$ 中的成员都属于 $A$ 并且具有性质 $cal(P)(x)$。
]<分类公理>
这样的集合 $B$ 通常记为 ${x in A : cal(P)(x)}$ 或者 ${x in A | cal(P)(x)}$。

通过它还可以定义空集为：$emptyset := {x in A | (x in x) and (x in.not x)}$，
也可以定义为 ${x in A | x eq.not x}$，这里 $A$ 是已经存在的集合。

#note-box[
  这个公理告诉我们，不能直接通过一元谓词造出一个集合，只能从给定集合中划分出一个子集。
于是经典的 Russell 悖论中的集合 ${x | x in.not x}$ 无法构造出来。
同时也不存在一个包罗万象的全集 $V$，使得 $R = {x in V | x in.not x}$ 起到 Russell 悖论的效果。
因为如果 $R in V$ 则 $R in R$ 和 $R in.not R$ 都能导出矛盾，于是 $V$ 不可能包含 $R$。也就是说 $V$ 不是全集。

因为我们禁止直接通过一元谓词构造这样的集合 ${x | P(x)}$，所有通过一元谓词构造的集合必须从一个更大的集合中选择一部分元素而得，
这就导致我们需要无穷公理，幂集公理等来构造足够大的背景集合。
]

#axiom(title: "配对公理")[
  #nonum-equation[
    $ (forall x)(forall y)(exists z)lr(size: #(1.3em), (x in z and y in z))$
  ]
  也就是任意两个集合 $x,y$，存在集合 $z$ 包含它们，我们把 $z$ 记为 ${x,y}$。
]<配对公理>
这个公理实际上不独立，它可以从替换公理得到：把 $A$ 设置为有两个成员的集合（通过空集来构造），比如 $A={0,1}$，
再设置 $cal(P)(u,v) = (u = 0 and v = x ) or (u = 1 and v = y)$。

把 ${x,x}$ 写作 ${x}$，称为单元素集合。配对公理还可以定义有序对为 $(a,b):= {{a},{a,b}}$

#axiom(title: "并集公理")[
  #nonum-equation[
    $ (forall A)(exists B)lr(size: #(1.4em), ( (forall x) [x in B <-> (exists y) y in A and x in y ]) ) $
  ]
  它断言每个集合 $A$ 都存在一个集合 $B$ 使得 $x in B$ 当且仅当 $x$ 是 $A$ 的某个成员的元素。
  一般把 $B$ 记为 $union.big A$。
]<并集公理>
注意，交集可以分类公理定义。

#axiom(title: "无穷公理")[
  #nonum-equation[
    $ (exists X)lr(( emptyset in X and (forall x)(x in X -> x union {x} in X) ), size: #(1.5em)) $
  ]
  也就是说存在一个包含无穷多元素的集合。最小的无穷集合是自然数集。
]<无穷公理>

#axiom(title: "幂集公理")[
  #nonum-equation[
    $(forall X)(exists Y)(forall x)[ x subset.eq X -> x in Y]$
  ]
  也就是说对每个集合都存在一个它的子集构成的集合，称为幂集，一般记作 $"Pow"(X)$。
]<幂集公理>

#axiom(title: "选择公理 AC")[
  #nonum-equation[
    $(forall X)(emptyset in.not X -> (exists f)[ (f: X -> union.big X) and  (forall a)(a in X -> f(a) in a) ])$
  ]
  这里 $f$ 是函数，关于函数的定义就采用通常的定义，也就是某种二元关系。
  因此它也可以表达为非空集合的集合的笛卡尔积非空。
]<选择公理>

== 序理论
我们可以在 ZFC 之上继续构建一阶理论。首先我们给出序关系。


#definition(title: "偏序")[
  *偏序(partial order)*关系是带等号的一阶理论，只有一个二元谓词，用 $<=$ 表示，并且用 $a >= b$ 来表示 $b <= a$，用 $a < b$ 来表示 $a <= b$ 以及 $a eq.not b$，
  没有函数项和常数项，有以下三条真公理：
  + 自反性：对任意 $a$，有 $a <= a$。
  + 反自反性：如果 $a <= b$ 与 $b <= a$ 则 $a=b$。
  + 传递性：如果 $a <= b$ 以及 $b <= c$ 则 $a <= c$。

  一个集合 $X$，如果是这个理论的模型，则称 $X$ 是*偏序集(poset)*，也用 $(X,<=)$ 来表示。
]
如果 $Y subset X$，那么显然 $Y$ 也是一个偏序集。

偏序理论中有一些概念值得注意：
#definition(title: "极值和最值")[
  设 $(X,<=)$ 是偏序集。则如果元素 $a$ 满足
  - 对任意 $a <= b$ 有 $a = b$，则称 $a$ 是极小值；
  - 对任意 $x in X$ 有 $a <= x$，则称 $a$ 是最小值。
  类似地可以定义极大值和最大值。
]

偏序集中有两种有单独命名：
#definition(title: "全序")[
  全序关系是在偏序理论的公理上再加上一条
  4. 完全性：$a <= b$ 与 $b <= a$ 至少有一个成立。

  全序也称线性序。全序模型称为*全续集(toset)*。
]

#definition(title: "良序")[
  偏序集 $S$ 如果每个非空子集都有最小值，那么 $S$ 称为*良序集(well-ordered set, woset)*。
]
显然良序集是全序集。

#definition(title: "截断")[
  在一个偏序集 $E$ 中, 子集 $S$ 如果满足条件 $x in S, y in E$ 以及
  $y <= x$ 推得出 $y in S$, 那么 $S$ 称为 $E$ 的一个*截断(segment)*.
]
显然 $E$ 的截断的任意交和并还是截断, 截断的截断还是截断, $E$ 自身以及空子集也是截断.

我们注意到，有一种截断，记作 $(<-, a)$ 或者 $S_a$，这里 $a in E$，表示所有满足 $y < a$ 的 $y in E$ 组成的集合，这种集合显然应该称为*区间(interval)*。

#proposition[
  良序集 $E$ 中的每个截断，如果不是 $E$ 自身的话，必然有形式 $(<-,a)$, 这里 $a in E$，这种形式的截断记为 $S_a$。
]
#proof[
  参见 @bourbaki2007théorie[Ch.III, Sec.2, Prop.2]。
]

在良序集上有
#theorem(title: "超限归纳法")[
  设 $(X,<=)$ 是良序集，$P(x)$ 是谓词，进而有集合 $A = {x in X | P(x) }$。
  如果截断 $( <- ,a) subset.eq A$ 推得出 $a in A$，也就是说如果所有比 $a$ 小的元素 $x$ 都具有性质 $P(x)$ 则 $a$ 也具有性质 $P(a)$， 
  那么 $A = X$，也就是说 $X$ 中所有元素 $x$ 都具有性质 $P(x)$。
]
#proof[
  假设 $A eq.not X$，那么 $X without A$ 是 $X$ 的非空子集，于是有最小元素 $a$。
  于是对任意 $x < a$ 都不属于 $X without A$ 也就是说 $x in A$，这样截断 $(<-,a) subset.eq A$，
  于是 $a in A$，这就出现了矛盾。
]

注意，超限归纳法不要求选择公理，它可以在任意良序集上使用，只是经常和良序定理配合而已。

#theorem(title: "超限递归构造")[
  设 $(X, <=)$ 是良序集，当 $u$ 是函数时，$T(u)$ 是一个集合。则存在一个集合 $U$ 和映射 $f:X -> U$ 使得对任意
  $x in X$ 有 $f(x) = T(f|(<-,x))$，这里 $f|(<-,x)$ 表示 $f$ 限制在截断 $(<-,x)$ 上得到的函数。
  这里 $U$ 和 $f$ 都是唯一的。
]
#proof[
  先证明唯一性：设有集合 $U'$ 与函数 $f'$ 也满足相关条件。设 $a in X$，如果对任意 $x < a$ 都有 $f(x) = f'(x)$，则
  $f|S_a = f'|S_a$，进而 $f(a) = T(f|S_a) = T(f'|S_a) = f'(a)$。于是根据超限归纳法就有 $f = f'$。

  对于存在性。设 $P(x)$ 表示存在函数 $f_x$，定义域为 $S_x$，且满足对任意 $y in S_x$ 有 $f_x (y) = T(f_x|S_y)$。
  根据前面证明的唯一性，这个 $f_x$ 是唯一的，并且对 $a<b$ 有 $f_a = f_b|S_a$，设每个 $y < x$ 都有 $P(y)$。注意到
  #nonum-equation[
    $ S_x = union.big_(y < x) S_y union {y} $
  ]
  因此当 $t in S_y, y<x$ 时定义 $f_x (t) = f_y (t)$，当 $t = y$ 时，定义 $f_x (t) = T(f_y)$。
  这是良定义，若有 $y < y' < x$，则对于 $t < y$ 时，$f_y (t) = f_y'(t)$ 因为唯一性，而对于 $t = y in S_y'$，有
  $f_y'(t) = T(f_y'|S_y) = T(f_y)$，最后这个等式依然来自唯一性。这样我们定义了 $S_x$ 上的 $f_x$，同时有
  $f_x|S_y = f_y$，因此 $f_x (y) = T(f_y) = T(f_x|S_y)$。 因此对 $x$ 来说 $P(x)$ 也成立，
  于是根据超限归纳法可得对任意 $x in X$ 都有 $P(x)$ 成立。

  如果 $X$ 没有最大元素，则 $X = union.big_(x in X) S_x$，于是 $f$ 可以定义为所有 $f_x$ 的并，也就是任意
  $t in X$ 都在某个 $S_x$ 当中，定义 $f(t) = f_x (t)$，这是良定义的并且对任意 $t in X$ 有 $f(t) = T(f|S_t)$。

  如果 $X$ 有最大元素 $a$，则 $X = {a} union union.big_(x in X) S_x$，此时所有 $f_x$ 的并记为 $g$，
  于是对于 $t eq.not a$ 定义 $f(t) = g(t)$，对于 $t = a$ 定义 $f(t) = T(g)$。
  显然 $f|S_a = g$，因此 $f$ 依然满足条件。这样就完成了存在性的证明。
]

#definition[
  设 $R,S$ 分别是集合 $X,Y$ 上的良序。我们说 $(X,R)$ 和 $(Y,S)$ 同构指的是存在双射 $s : X -> Y$ 使得
  $s(a) <= ^S s(b)$ 当且仅当 $a <= ^R b$。
]

#theorem[
  设 $E,F$ 是两个良序集。那么下列两个断言至少有一个为真：
  + 存在唯一一个从 $E$ 到 $F$ 的某个截断的同构；
  + 存在唯一一个从 $F$ 到 $E$ 的某个截断的同构。
]<良序集同构二选一>
#proof[
  参见 @bourbaki2007théorie[Ch.III, Sec.2, Th.3]。这个定理的证明需要用到后面才能序数和证明的 Zorn 引理，
  但是序数和证明那几个有关定理并不需要本定理及其推论。
]

#corollary[
  良序集 $E$ 到它自身的某个截断的唯一一个同构就是单位映射 $id_E$。
]

#corollary[
  设 $E,F$ 是两个良序集。如果存在从 $E$ 到 $F$ 的截断 $T$ 的同构 $f$，又有从 $F$ 到 $E$ 的截断 $S$ 的同构 $g$，
  那么 $S=E, T=F$, 并且 $g,f$ 互为逆映射.
]

== 序数
序数是自然数用于排序的那部分功能的推广。从直观上可以把序数定义为良序集之间的同构的等价类，但是这样定义的序数太大而不是集合，
导致讨论序数的集合时遇到困难。因此采用 von Neumann 给出的定义，把序数定义为小于它的序数构成的良序集：
#definition[
  *序数(ordinal)*指的是集合 $alpha$，且满足如下条件：
  - $(alpha, in)$ 是良序集, 这里把 $x,y in alpha, x in y$ 定义为 $x < y$
  - $alpha$ 是传递集: 如果 $gamma in beta, beta in alpha$, 那么 $gamma in alpha$
]

#remark[
  在 $(alpha,in)$ 是全序集的前提下, $alpha$ 的任意非空子集 $x$ 都存在最小元素 $y$ 这个断言可以表示为：
  #nonum-equation[
    $ emptyset eq.not x subset.eq alpha ==> (exists y in x) ( x inter y = emptyset) $
  ]
  根据序数定义，$x$ 的最小元素 $y$ 不能和 $x$ 相交。而如果 $x$ 中某个元素 $y$ 和 $x$ 不相交，
  那么就是说对每个 $z in x$ 都有 $z in.not y$ 于是根据全序关系的三歧性可以得到 $y <= z$ 也就是说 $y$ 是 $x$ 的最小元素。
]

#example[
  容易看出我们可以定义自然数为 $0 = emptyset, 1 = {emptyset}, 2 = { emptyset, {{ emptyset }}}, dots$
]

关于序数有一些性质：
#proposition[
  + 序数的元素也是序数。
  + 设 $alpha,beta$ 是序数, 则 $beta in alpha$ 当且仅当 $beta subset alpha$。
]<序数元素是序数以及从属是包含>
#proof[
  对于 1，设 $alpha$ 是序数，$beta in alpha$。根据序数定义可知 $beta subset alpha$，于是 $beta$ 继承了 $alpha$ 的良序结构。
  然后假设 $delta in gamma in beta$。由 $alpha$ 是序数可知 $delta in alpha$。
  而 $beta$ 也属于 $alpha$, 并且 $in$ 在 $alpha$ 当中构成全序关系，
  因此 $delta in beta, delta = beta, beta in delta$ 三者必然有且只有一个成立，而后两种情况会导出
  $beta in gamma in beta in alpha$ 和 $beta in delta in gamma in beta in alpha$。
  它们都是不成立的：否则会出现一个关于 $in$ 关系的无穷递降序列
    #nonum-equation[
      $ dots in x_(n+1) in x_n in dots in x_1 in alpha $
    ]
    根据 $alpha$ 是传递集以及数学归纳法可以得到每个 $x_n$ 都是 $alpha$ 的元素, 于是 ${ x_1, x_2, dots }$ 是 $alpha$ 的非空子集。
    而 $alpha$ 在 $in$ 关系下是良序集，因此 $x$ 中存在最小的一个 $x_n$。然而必然会有 $x_(n+1) in x_n, x_(n+1) in x$，
    这样 $x_n$ 就不是 $x$ 的最小元素，就出现了矛盾。

    对于 2，假设 $beta in alpha$，那么根据传递集性质有 $beta subset.eq alpha$。若 $beta = alpha$，那么会出现
    $beta in beta in alpha$ 跟上面证明的不存在无穷递降序列矛盾，因此 $beta subset alpha$。
    
    反过来，假设 $beta subset alpha$. 那么 $emptyset eq.not alpha without beta subset.eq alpha$，
    也就是存在最小元素 $x in alpha without beta$ 使得 $x inter (alpha without beta) = emptyset$。
    再由序数传递性可得 $x subset.eq alpha$，或者 $x = x inter alpha$。因此 $x without beta = emptyset$, 即 $x subset.eq beta$。
    从区间上来看 $alpha without beta$ 有点像一个下有界的区间，因此找到这个区间的下端点就能表达 $beta$，下面再证明这个下端点就是 $beta$。

    假设 $beta eq.not x$，也就是有 $y in beta without x$，那么从 $x in.not beta$ 知道 $x eq.not y$。
    而 $y in beta subset alpha$ 结合 $x in alpha$ 以及 $y in.not x$，那么根据全序关系必然有 $x in y$。
    另外根据序数的传递性可得 $x,y$ 都是序数，这样根据上面证明的必要性可以得到 $x subset y$。
    $y in beta$ 推出 $y subset beta$，这样 $y inter (beta without x) = y without x eq.not emptyset$。
    也就是说, 对于任意 $y in beta without x$, $y inter (beta without x)$ 非空，这和 $beta$ 是良序矛盾，因此 $beta = x in alpha$.
]

#corollary[
  序数 $alpha$ 中的元素关于 $subset.eq$ 也是良序集。
]

#proposition[
  任意个序数的交还是序数。
]
#proof[
  设有非空指标集 $I$ 和序数集 $(alpha_i)_(i in I)$. 则
  #nonum-equation[
    $ x in inter.big_(i in I) alpha_i ==> (forall i in I) x in alpha_i ==> 
    (forall i in I) x subset.eq alpha_i ==> x subset.eq inter.big_(i in I) alpha_i $
  ]
  因此 $inter_i alpha_i$ 是传递集。而 $inter_i alpha_i$ 继承了任意一个 $alpha_i$ 的良序结构。
]

#corollary[
  任意序数组成的集合，在 $subset.eq$ 关系下有最小序数。
]
#proof[
  设有非空指标集 $I$ 和序数集 $(alpha_i)_(i in I)$。如果对任意 $j in I$ 都有 $alpha_j eq.not inter_i alpha_i$，
  那么首先 $inter_i alpha_i$ 是序数，并且是每个 $alpha_j$ 的真子集，于是根据 @序数元素是序数以及从属是包含 得到序数
  $inter_i alpha_i in alpha_j$，这样就有
  #nonum-equation[
    $ inter_i alpha_i in inter_i alpha_i $
  ]
  这和不存在 $in$ 关系下的序数的无穷递降链矛盾。因此至少有一个 $alpha_j = inter_i alpha_i$，于是它就是序数集 $(alpha_i)_(i in I)$ 的最小序数。
]

现在我们看到，序数在包含关系下实际上是良序，也就是说任意序数组成的集合都是良序集。
如果序数 $alpha$ 是序数 $beta$ 的真子集，那么我们写作 $alpha < beta$。
显然 $alpha < beta$ 时，根据 @序数元素是序数以及从属是包含 可以得到 $alpha$ 是 $beta$ 的一个截断。
而根据 @良序集同构二选一 可以得到两个序数同构当且仅当它们相等。

进一步，由序数构成的集合在从属关系 $in$ 下总是有最小元素，因为总可以先考虑包含关系得到包含关系下的最小元素，然后通过 @序数元素是序数以及从属是包含 
得到从属关系下的最小元素。因此在证明某个由序数组成的集合是序数时，只需要证明它是传递集即可。

#note-box[
  全体序数构成的真类记为 $bold("Ord")$，但是在 ZFC 中不讨论真类，它将在下一章讨论。
]

对于之前的直观，我们由下列命题保证：
#theorem(title: "Mirimanoff - von Neumann")[
  对任意良序集 $(X,<=)$，存在唯一一个序数 $alpha$ 使得 $(X,<=)$ 和 $(alpha, in)$ 同构。
]<良序集和序数同构>
#proof[
  两个序数同构当且仅当它们相等，因此有了唯一性。

  用超限递归可以定义 $X$ 上唯一的函数 $f$ 使得 $f(a) = emptyset$ 这里 $a$ 是 $X$ 当中的最小元素，以及对任意 $x in X$ 有
  #nonum-equation[
    $ f(x) = { f(y) | y < x } = union.big_(y < x){f(y)} $
  ]
  显然 $y < x$ 当且仅当 $f(y) in f(x)$，这使得 $f$ 的像在 $in$ 下称为良序，以及 $f$ 的像是传递集，因此 $f$ 的像是序数，
  并且 $f$ 是唯一一个同构，根据超限递归。
]

下面讨论序数算数：
#lemma(title: "后继序数")[
  每个序数 $alpha$ 的后继序数, 也就是大于 $alpha$ 的最小序数, 记为 $alpha+1$, 是 $alpha union { alpha }$.
]<后继序数>
#proof[
  若 $x in alpha union {alpha}$，那么 $x in alpha$ 或者 $x = alpha$，根据 $alpha$ 的传递性总有
  #nonum-equation($x subset.eq alpha subset.eq alpha union {alpha}$)
  因此 $alpha union {alpha}$ 是传递集，根据 @序数元素是序数以及从属是包含 可知它还是由序数组成的，因此也是序数。

  而 $alpha in alpha union {alpha}$，因此 $alpha < alpha union {alpha}$。
  如果 $beta > alpha$，那么 $beta eq.not alpha$，并且 $beta in.not alpha$，
  于是 $beta in.not alpha union {alpha}$，也就是 $beta >= alpha union {alpha}$, 即后者是大于 $alpha$ 的最小序数。
]

#lemma(title: "最小上界序数")[
  若 $A$ 是序数组成的集合，那么 $union.big A$ 是 $A$ 的最小上界序数，记为 $sup A$。
]<最小上界序数>
#proof[
  传递集的并还是传递集。$A$ 中序数的元素还是序数，因此 $union.big A$ 就是序数组成的传递集，于是也是序数。
  若序数 $x in A$ 则 $x subset.eq union.big A$，进而 $x in union.big A$，也就是说
  $union.big A$ 是 $A$ 的上界序数。如果有序数 $beta$ 使得对任意 $x in A$ 都有 $x in beta$，则 $x subset beta$，
  于是 $union.big A subset beta$ 进而 $union.big A in beta$，因此 $union.big A$ 是 $A$ 的最小上界。
]

#lemma[
  如果 $alpha$ 是序数，则必然是下列三种情况之一：
  + $alpha = 0$；
  + 存在序数 $beta$ 使得 $alpha = beta + 1$，即 $alpha$ 是后继序数；
  + $alpha = union.big_(lambda < alpha) lambda$，此时称 $alpha$ 是极限序数。
]<序数的三种情况>
#proof[
  假设 $alpha eq.not 0$。那么注意到 $alpha$ 有最大元素 $beta in alpha$ 当且仅当 
  $beta + 1 subset.eq alpha$ 并且对任意 $x in alpha$ 有 $x <= beta$。
  此时 $x <= beta$ 有 $x in beta$ 或者 $x = beta$ 两种情况，不管哪种情况都有 $x in beta union {beta} = beta + 1$，
  因此 $alpha = beta + 1$。

  而当 $alpha$ 没有最大元素时，也就是对任意 $x in alpha$，都存在一个 $alpha$ 当中更大的序数 $y > x$ 或者
  $x in y$，这样 $alpha subset.eq union.big alpha$, 注意 $alpha supset.eq union.big alpha$ 总是成立。
]

#note-box[
  显然自然数集 $NN$ 就是一个极限序数，实际上它是第一个极限序数，记为 $omega_0$。
]

现在可以定义序数运算了：
#definition(title: "序数和")[
  + $alpha + 0 = alpha$
  + $alpha + beta = (alpha + gamma) + 1$, 如果 $beta = gamma + 1$ 是后继序数
  + $alpha + beta = union.big_(gamma < beta) (alpha + gamma)$, 如果 $beta$ 是极限序数.
]

#definition(title: "序数积")[
  + $alpha dot 0 = 0$
  + $alpha dot beta = alpha dot gamma + alpha$，如果 $beta = gamma + 1$ 是后继序数
  + $alpha dot beta = union.big_(gamma < beta) (alpha dot gamma)$，如果 $beta$ 是极限序数
]

超限归纳法和超限递归可以推广到序数上：
#proposition(title: "序数的超限归纳法")[
  设 $P(x)$ 是一元谓词公式，如果对任意序数 $alpha$ 都有
  #nonum-equation[
    $ ((forall beta < alpha) P(beta)) --> P(alpha) $
  ]
  则对每个序数 $alpha$ 都有 $P(alpha)$ 成立。
]
#proof[
  设序数 $alpha$ 使 $P(alpha)$ 不成立，那么集合 $A = {beta in alpha + 1 | not P(beta)}$ 便是 $alpha + 1$ 的非空子集，
  必然存在一个最小元素 $gamma$，于是 $beta < gamma$ 时，它们不属于 $A$，这说明有 $P(beta)$，于是根据条件有 $P(gamma)$，
  这和 $gamma in A$ 矛盾。
]

#proposition(title: "序数的超限递归")[
  设 $G_1, G_2, G_3$ 给集合 $u$ 指定集合 $G_1(u),G_2(u),G_3(u)$，则对每个序数 $alpha$ 存在唯一集合 $A_alpha$ 使得
  - $A_0 = G_1(emptyset)$
  - $A_(alpha + 1) = G_2(A_alpha)$
  - $A_alpha = G_3({A_beta | beta < alpha})$，这里 $alpha$ 是非零极限序数。
]
#proof[
  这直接来自 @序数的三种情况。
]

== 选择公理
在承认 ZF 的前提下，@选择公理[选择公理] 有几个等价命题，其中最出名的便是 Zorn 引理和良序定理。

#theorem(title: "良序定理")[
  每个集合上都存在良序结构。
]
#proof(title: "从选择公理出发证明")[
  设 $X$ 是集合。为了良序化它，用超限递归构造一个序数序列穷举 $X$。设 $scr(S)$ 是 $X$ 的非空子集的集合，
  $f$ 是 $scr(S)$ 上的选择函数（存在性通过选择公理保证）。现在，对每个序数 $alpha$，定义
  + $a_0 = f(X)$
  + $a_alpha = f(X without {a_lambda | lambda < alpha})$ 如果 $X without {a_lambda | lambda < alpha}$ 非空
  注意 $lambda < alpha + 1$ 当且仅当 $lambda <= alpha$，因此上面实际上包含了全部的情况。
  
  注意到 $a_alpha in X without {a_lambda | lambda < alpha}$ 因此 $a_alpha$ 和 $a_lambda,lambda < alpha$ 都不相等。
  因此 $alpha$ 与 ${a_lambda | lambda < alpha} subset.eq X$ 一一对应，于是必然存在一个序数 $beta$ 使得
  $X = {a_lambda | lambda < beta}$，否则 $X$ 会包含所有的序数，就不是集合。这样 $X$ 和 $beta$ 有双射，于是 $X$ 就可以定义良序了。
]

#theorem(title: "Zorn 引理")[
  任意非空偏序集 $X$ 当中，如果每个全序子集有上界，那么 $X$ 中存在极大元素。
]
#proof(title: "从良序定理出发")[
  根据良序定理 $X$ 有一良序，因此 $X$ 可以写作 ${a_lambda | lambda < alpha}$ 这种形式。
  然后我们要构造也尽可能长的全序子集，这样这个全序子集的最大元素就是 $X$ 的极大元素。
  定义 $A : alpha -> "Pow"(X)$：
  #nonum-equation[
    $ A_0 &= emptyset \
    A_(xi + 1) &= cases(A_xi union {a_xi} "如果" A_xi union {a_xi} "是全序集", A_xi "如果不是") \
    A_lambda &= union.big_(xi < lambda) A_xi $
  ]
  现在 $A_alpha$ 是一个尽可能长的全序子集：假设有全序子集 $T supset.eq A_alpha$，那么对任意 $a_beta in T$，
  由于 $A_beta subset A_alpha$，我们有 $A_(beta + 1) = A_beta union {a_beta} subset.eq A_alpha$，因此 $a_beta in A_alpha$。
  由于 $A_alpha$ 的上界 $a$ 一定使得 $A_alpha union {a}$ 是全序集，因此 $a in A_alpha$，也就是说 $a$ 是 $A_alpha$ 的最大值。
  如果有 $b >= a$，同样道理可得 $b in A_alpha$，这样 $b <= a$，因此 $a = b$ 换句话说 $a$ 是 $X$ 的极大元素。
]

#proposition[
  在 ZF 的前提下，如果 Zorn 引理成立，则选择公理成立：
  - 给定一族非空集合 ${X_i}_(i in I)$，存在也映射 $f: I -> union.big_(i in I) X_i$，使得对任意 $i in I$ 有 $f(i) in X_i$。
]
#proof[
  用 $X$ 表示二元组 $(J,f)$ 构成的偏序集，其中 $J subset I$，而 $f : J -> union.big_(x in I) X_i$ 是映射，使得对任意
  $i in J$ 有 $f(i) in X_i$。定义 $(J,f) <= (J',f')$ 为 $J subset.eq J'$ 以及 $f = f'|J$。
  这样显然每个链都有上界。

  于是根据前提，$X$ 有一个极大元 $(J,f)$。断言 $J = I$，否则有 $i_0 in I without J$，于是令 $J' = J union {i_0}$，
  以及 $f': J' -> union.big_(i in I) X_i$ 使得 $f'|J = f, f'(i_0) in X_i_0$。
  最后这一步是在 $X_i_0$ 中任取一个元素为 $f'(i_0)$ 的值，这是可以做到的因为 $X_i_0$ 非空。这样 $(J,f) < (J',f')$ 与 $(J,f)$ 是极大元素矛盾，
  所以 $J = I$ 从而 $f$ 就是我们要的选择函数。
]

== 基数
序数用来给对象排序，而基数则是用来给集合比大小。

#definition[
  一个集合 $X$ 和集合 $Y$ 是*等势的(equipotent)*指的是存在一个从 $X$ 到 $Y$ 的双射，记作 $abs(X) = abs(Y)$。
]

直观的说应该把基数定义为上面关系的等价类，但是这样一来每个基数成为真类，就不能把一些基数组成集合。 
参考无穷集的定义：无穷集指的是不能和子集等势的集合，我们模仿其定义基数：

#definition[
  一个序数如果不能和比它小的序数等势，那么就称它为*基数(cardinal)*。
]

#note-box[
  全体基数构成的真类记为 $bold("Card")$，但是在 ZFC 中不讨论真类，它将在下一章讨论。
]

自然数集显然是基数，用 $omega$ 表示，具有这个基数的集合就是可数集。而每个自然数也是基数，我们称其为有限基数。
所以对于有限集来说，基数和序数是一样的，但是对无限集来说就需要分开讨论了。

前面的直观由以下命题保证：
#proposition[
  对任意集合 $X$，存在唯一基数 $alpha$ 和它等势，也就是满足这个条件的最小序数。这个 $alpha$ 称为 $X$ 的*势*, 记为 $abs(X)$.
]
#proof[
    根据良序定理，$X$ 上有良序，然后根据 @良序集和序数同构，存在一个序数 $gamma$ 和 $X$ 同构，特别地和 $X$ 双射。集合
    #nonum-equation[
      $ A := { beta in gamma + 1 | abs(X) = abs(beta)  } $
    ]
    是序数 $gamma + 1$ 的非空子集，因此有最小元素 $alpha$。显然所有和 $X$ 等势的序数都不能小于 $alpha$，
    也就是说它就是和 $X$ 等势的最小序数。

    如果 $alpha$ 能和比自己小的序数 $beta$ 建立双射，则它也和 $X$ 等势，这与 $alpha$ 是最小的矛盾，因此 $alpha$ 是基数。
]

由于任何序数组成的集合都是良序集，这意味着集合的势可以进行比较。

#theorem(title: "Cantor-Bernstein-Schroeder 定理")[
  设 $A,B$ 是集合，如果有单射 $f: A -> B$ 和单射 $g: B -> A$，那么存在双射 $h: A -> B$。
]<CBS定理>

#definition(title: "加法和乘法")[
  基数加法定义为 $sum_(i in I) abs(X_i) = abs(union.big.sq_(i in I) X_i)$。
  基数乘法定义为 $product_(i in I) abs(X_i) = abs(product_(i in I) X_i)$.
]

#definition(title: "指数")[
  基数的指数定义为 $abs(Y)^abs(X) = abs(Y^X)$，其中 $Y^X$ 表示所有 $X$ 到 $Y$ 的映射组成的集合。
]

值得注意的一个情况是 $Y = 2$ 时，这里 $2$ 定义为 ${0,1}$。那么从 $X$ 到 $2$ 的映射实际上是子集指示函数，
每个映射和 $X$ 的一个子集对应，于是 $2^X$ 实际上是 $X$ 的幂集。

#definition(title: "后继基数和极限基数")[
  对序数 $alpha$，用 $alpha^+$ 表示大于 $alpha$ 的最小基数，称为*后继基数*，不是后继基数的称为极限基数。
]

我们需要说明后继序数确实存在：
#lemma(title: "Hartogs 数")[
  对任意集合 $X$，下列构造
  #nonum-equation[
    $ alpha = {beta in bold("Ord") | exists i: beta arrow.r.hook X} $
  ]
  是集合，并且还是不与 $X$ 等势的最小序数。
]
#proof[
  首先根据集合论公理 $"Pow"(X times X)$ 是集合，因此根据 @分类公理 $X$ 上的良序关系构成集合，
  进而根据 @良序集和序数同构，每个 $X$ 上的良序和唯一一个序数同构，因此和 $X$ 等势的序数构成集合（注意序数的自同构只有单位映射），
  而这些序数的并就是 $alpha$。

  $alpha$ 是传递集：设 $beta in alpha$，这说明 $alpha$ 到 $X$ 有单射，而 $gamma in beta$ 根据
  @序数元素是序数以及从属是包含 可知有包含关系 $gamma subset beta$，这样 $gamma$ 到 $X$ 也有单射了，因此 $gamma in alpha$。
  $alpha$ 是序数构成的集合，因此是良序集，这样 $alpha$ 就是序数了。

  不存在从 $alpha$ 到 $X$ 的单射，否则 $alpha in alpha$ 会出现无穷递降序列。
  最后 $alpha$ 是不存在到 $X$ 的单射的最小序数，因为比 $alpha$ 小的序数都属于 $alpha$，也就是说存在到 $X$ 的单射。
]

根据上述引理，对每个序数 $alpha$，都存在一个最小的不与其等势的序数 $alpha'$。
这个 $alpha'$ 是基数，因为比它小的序数都和 $alpha$ 等势了，因此不可能和 $alpha'$ 等势，于是这个 $alpha'$ 就是 $alpha$ 的后继基数。

现在我们可以建立从序数到基数的对应了：

#proposition(title: "Aleph 数")[
  对每个序数 $alpha$，有唯一基数 $aleph_alpha$，称为 *Aleph 数*，按照如下方式超限递归构造：
  + $aleph_0 = omega$
  + $aleph_(alpha + 1) = (aleph_alpha)^+$
  + $aleph_alpha = union.big_(gamma < alpha) aleph_gamma$，这里 $alpha$ 是极限序数

  并且这个对应是双射。
]
#proof[
  构造过程只有极限序数的情况需要说明一下如此定义的确实是基数：首先根据 @最小上界序数， 
  $union.big_(gamma < alpha) aleph_gamma$ 是序数，比它小的序数 $beta$ 必然比某个 $aleph_gamma$ 小，
  而 $beta$ 不能和 $aleph_gamma$ 建立双射。如果 $beta$ 能和整个并集建立双射，意味着这个 $aleph_gamma$ 有一个到更小的序数 $beta$ 的单射，
  于是根据 Cantor-Bernstein-Schroeder 定理，$alpha_gamma$ 和 $beta$ 等势，这是不可能的。

  单射：当 $alpha < beta$ 时，用超限归纳法证明 $aleph_alpha < aleph_beta$。设 $P(beta)$ 是谓词
  #nonum-equation[
    $ P(beta) := (forall alpha < beta) aleph_alpha < aleph_beta $
  ]
  如果对任意 $gamma < beta$ 都有 $P(gamma)$ 成立，则 $P(beta)$ 成立：
  - $beta = gamma + 1$ 是后继，则如果 $alpha = gamma$ 就有 $aleph_alpha < (aleph_gamma)^+ = aleph_beta$，如果 $alpha < gamma$ 则有 $aleph_alpha < aleph_gamma <(aleph_gamma)^+ = aleph_beta$。
  - $beta$ 是极限序数，此时 $alpha + 1 < beta$，于是 $aleph_(alpha + 1) in {aleph_gamma | gamma <beta}$，进而 $aleph_(alpha + 1) subset aleph_beta$，因此 $aleph_alpha < aleph_beta$。
  这样就证明了 $alpha mapsto aleph_alpha$ 是单射。

  假设有一个最小的无限基数 $kappa$ 使得对任意 $alpha$ 都有 $aleph_alpha eq.not kappa$，则考虑集合
  #nonum-equation[
    $ S = {lambda in kappa | lambda in bold("ICn")} $
  ]
  这里 $bold("ICn")$ 表示无限基数，于是 $S$ 是 $kappa$ 的非空子集，里面的每个基数都有形式 $aleph_beta$。
  我们刚刚证明了单射性，也就是说每个这种形式的基数 $aleph_beta$ 都只有唯一一个序数 $beta$ 与之对应，
  这样利用 @替换公理 得到有一个集合
  #nonum-equation[
    $ A = {gamma in bold("Ord") | aleph_gamma in S} $
  ]
  这个集合是传递集：设有 $gamma in beta in A$，则 $beta in A$ 推得出 $aleph_beta in S$；
  而 $gamma in beta$ 意味着 $aleph_gamma < aleph_beta in kappa$，因此根据序数传递性就得到 $aleph_gamma in kappa$，进而 $gamma in A$。
  这样 $A$ 是由序数构成的传递集，因此也是序数，记为 $beta$。这样 $A = beta$ 中的元素就是小于 $beta$ 的序数，这样有
  #nonum-equation[
    $ S = {aleph_gamma | gamma < beta} $
  ]
  根据序数上确界，$aleph_beta <= kappa$。如果 $aleph_beta < kappa$，则 $aleph_beta in S$，进而 $beta in A = beta$ 这是不可能的。
  因此 $aleph_beta = kappa$，然而这也是不可能的因为 $kappa$ 不能写为这种形式。这样我们就导出了矛盾，证明了 $alpha mapsto aleph_alpha$ 是满射。
]

#proposition(title: "连续统假设")[
  - $2^(aleph_0) = aleph_1$，等价描述是不存在基数位于自然数和实数的势之间。
  另外还有*广义连续统假设*
  - 对任意序数 $alpha$，$2^(aleph_alpha) = aleph_(alpha + 1)$.
]
这个命题与 ZFC 公理独立，肯定的相容性由 Kurt Godel 于 1940 年通过他的可构造宇宙来证明，否定的相容性由 Paul Cohen 于 1963 年通过力迫法来证明。

#proposition[
  设 $kappa, lambda$ 是无限基数，则
  #nonum-equation[
    $ kappa + lambda = kappa lambda = max{kappa,lambda}$
  ]
]<基数运算性质>
#proof[
  不妨设 $kappa <= lambda$，则有
  #nonum-equation[
    $lambda <= kappa + lambda <= 2lambda <= kappa lambda <= lambda^2$
  ]
  因此只需证明 $lambda^2 <= lambda$ 即可。我们前面已经证明 $alpha mapsto aleph_alpha$ 是从 $bold("Ord")$ 到 $bold("Card")$ 的双射，
  所以我们设 $lambda = aleph_alpha$ 并对 $alpha$ 做超限归纳。$alpha = 0$ 时已知，实际上就是可数集和可数集的乘积还是可数集。

  假设对每个序数 $beta < alpha$ 都有 $aleph_beta^2 <= aleph_beta$。因此对每个小于 $lambda = aleph_alpha$ 的序数 $gamma$ 都有
  $|gamma|^2 = |gamma|$。 现在给 $lambda^2$ 赋予一个序关系：
  #nonum-equation[
    $(a,b) < (c,d) <==> (max{a,b}, a, b) < (max{c,d}, c, d)$
  ]
  后者采用 $lambda^3$ 的字典序，而 $lambda^3$ 的字典序是良序，因此我们定义在 $lambda^2$ 的这个序也是良序。可以验证
  #nonum-equation[
    $lambda^2_(<=(a,a)) = {(c,d) in lambda^2 | (c,d) <= (a,a)} = {c in lambda | c <= a }^2 = lambda_(<=a)^2$
  ]
  注意到 $lambda_(<=a)$ 是小于 $lambda$ 的序数，因此根据归纳假设以及序数乘法的定义有：
  #nonum-equation[
    $|lambda_(<=(a,a))^2| = |lambda_(<=a)^2| = |lambda_(<=a)|^2 = |lambda_(<=a)| < lambda$
  ]
  于是 $lambda^2_(<=(a,a))$ 的序型小于 $lambda$，否则 $lambda$ 有到 $lambda^2_(<=(a,a))$ 的单射，与上式矛盾。然后注意到
  $lambda^2$ 的序型是 $lambda^2_(<=(a,a))$ 序型的上确界，因为 $lambda^2_(<=(a,a))$ 是一个共尾子集。
  因此 $lambda^2$ 的序型必然小于等于 $lambda$，那么 $lambda^2$ 的基数必然也小于等于 $lambda$，或者可以写作 $aleph_alpha^2 <= aleph_alpha$。
]