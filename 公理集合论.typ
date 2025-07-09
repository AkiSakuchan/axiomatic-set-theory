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

=== 序关系
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

#definition(title: "截断")[
  在一个偏序集 $E$ 中, 子集 $S$ 如果满足条件 $x in S, y in E$ 以及
  $y <= x$ 推得出 $y in S$, 那么 $S$ 称为 $E$ 的一个*截断(segment)*.
]
显然 $E$ 的截断的任意交和并还是截断, 截断的截断还是截断, $E$ 自身以及空子集也是截断.

我们注意到，有一种截断，记作 $(<-, a)$，这里 $a in E$，表示所有满足 $y < a$ 的 $y in E$ 组成的集合，这种集合显然应该称为*区间(interval)*。

#proposition[
  良序集 $E$ 中的每个截断，如果不是 $E$ 自身的话，必然有形式 $(<-,a)$, 这里 $a in E$。
]