#import "book-style.typ": *
#import "@preview/theorion:0.3.3": *
#import "@preview/commute:0.3.0": node, arr, commutative-diagram
#import cosmos.rainbow: *
#show: show-theorion

#let vdash = math.class("normal", math.tack.r)
#let Vdash = math.class("normal", math.tack.r.double)

= ZFC 集合论
现在我们可以谈论公理集合论了。
- 公理集合论是一种带等号的一阶理论（参见 @等号公理）。
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
首先满足条件的 $cal(P)(x,y)$ 实际上可以定义一个"函数" $F$，把 $F(x) = y$ 定义为 $P(x,y)$，后半部分实际上要求对任意集合
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

== 序数
我们可以在 ZFC 之上继续构建一阶理论。首先我们给出序关系。


#definition(title: "偏序")[
  *偏序(partial order)*理论是带等号的一阶理论，只有一个二元谓词，用 $<=$ 表示，并且用 $a >= b$ 来表示 $b <= a$，用 $a < b$ 来表示 $a <= b$ 以及 $a eq.not b$，
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
  全序理论是在偏序理论的公理上再加上一条
  4. 完全性：$a <= b$ 与 $b <= a$ 至少有一个成立。

  全序也称线性序。全序模型称为*全续集(toset)*。
]

#definition(title: "良序集")[
  偏序集 $S$ 如果每个非空子集都有最小值，那么 $S$ 称为*良序集(well-ordered set, woset)*。
]
显然良序集是全序集。

#definition(title: "截断")[
  在一个偏序集 $E$ 中, 子集 $S$ 如果满足条件 $x in S, y in E$ 以及
  $y <= x$ 推得出 $y in S$, 那么 $S$ 称为 $E$ 的一个*截断(segment)*.
]
显然 $E$ 的截断的任意交和并还是截断, 截断的截断还是截断, $E$ 自身以及空子集也是截断.

我们注意到，有一种截断，记作 $(<-, a)$，这里 $a in E$，表示所有满足 $y < a$ 的 $y in E$ 组成的集合，这种集合显然应该称为*区间(interval)*。

#proposition[
  良序集 $E$ 中的每个截断，如果不是 $E$ 自身的话，必然有形式 $(<-,a)$, 这里 $a in E$。
]
#proof[
  参见 @bourbaki2007théorie[Ch.III, Sec.2, Prop.2]。
]

在良序集上有
#theorem(title: "超限归纳法")[
  设 $(X,<=)$ 是良序集，$P(x)$ 是谓词，进而有集合 $A = {x in X | P(x) }$。
  如果截断 $( <- ,a) subset.eq A$ 蕴含着 $a in A$，也就是说如果所有比 $a$ 小的元素 $x$ 都具有性质 $P(x)$ 则 $a$ 也具有性质 $P(a)$， 
  那么 $A = X$，也就是说 $X$ 中所有元素 $x$ 都具有性质 $P(x)$。
]
注意，超限归纳法不要求选择公理，它可以在任意良序集上使用，只是经常和良序定理配合而已。

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
  参见 @bourbaki2007théorie[Ch.III, Sec.2, Th.3]。
]

#corollary[
  良序集 $E$ 到它自身的某个截断的唯一一个同构就是单位映射 $id_E$。
]

#corollary[
  设 $E,F$ 是两个良序集。如果存在从 $E$ 到 $F$ 的截断 $T$ 的同构 $f$，又有从 $F$ 到 $E$ 的截断 $S$ 的同构 $g$，
  那么 $S=E, T=F$, 并且 $g,f$ 互为逆映射.
]

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

现在我们看到，序数实际上满足良序关系，也就是说任意序数组成的集合都是良序集。
如果序数 $alpha$ 是序数 $beta$ 的真子集，那么我们写作 $alpha < beta$。
显然 $alpha < beta$ 时，根据 @序数元素是序数以及从属是包含 可以得到 $alpha$ 是 $beta$ 的一个截断。
而根据 @良序集同构二选一 可以得到两个序数同构当且仅当它们相等。

由序数构成的集合总是有最小元素，不管是在包含关系 $subset.eq$ 还是从属关系 $in$ 下。
因为总可以先考虑包含关系得到包含关系下的最小元素，然后通过 @序数元素是序数以及从属是包含 得到从属关系下的最小元素。
因此在证明某个集合是序数时，只需要证明它是传递集以及具有全序关系即可。

对于之前的直观，我们由下列命题保证：
#theorem(title: "Mirimanoff - von Neumann")[
  对任意良序集 $(X,<=)$，存在唯一一个序数 $alpha$ 使得 $(X,<=)$ 和 $(alpha, in)$ 同构。
]
#proof[
  两个序数同构当且仅当它们相等，因此有了唯一性。

  用超限归纳法可以定义 $X$ 上的函数 $f$ 使得对任意 $x in X$ 有 $f(a) = emptyset$ 这里 $a$ 是 $X$ 当中的最小元素，以及
  #nonum-equation[
    $ f(x) = { f(y) | y < x } $
  ]
  容易验证 $f$ 的像是传递集，并且 $f(y) in f(x)$ 当且仅当 $y < x$。因此 $f$ 的像是序数，并且 $f$ 是唯一一个同构 (@良序集同构二选一).
]