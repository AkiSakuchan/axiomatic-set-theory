#import "book-style.typ": *
#import "@preview/theorion:0.3.3": *
#import "@preview/commute:0.3.0": node, arr, commutative-diagram
#import cosmos.rainbow: *


#show: show-theorion

#show: rest => book(title: [公理集合论], 
authors: "Aki Sakuchan", 
bib-file: "references.bib",
rest)

#let vdash = math.class("normal", math.tack.r)
#let Vdash = math.class("normal", math.tack.r.double)

= 命题逻辑
本笔记只通过自然语言的方式给出这些语法的语义。因为命题逻辑中的构造步骤都是有限的，涉及到的集合都是至多可数的，因此可以用自然语言去讨论是安全的。

== 形式语法
对于语法，我们只需要关注它们在形式上是否合规，关注每项和其他项之间的关系以及如何互动，不关注它们的含义。

#definition[
  一个*形式理论* $scr(S)$ 由以下部分组成
  #enum[
    至多可数个符号的集合。$scr(S)$ 的符号组成的有限长字符串称为 $scr(S)$ 的*表达式*。
  ][
    表达式中选择一部分，称为*合式公式(well-formed formula, WFF)*，并且有一个规则能在有限步内判断一个表达式是否是合式公式。
  ][
    由一部分合式公式被称为 $scr(S)$ 的*公理*，此时 $scr(S)$ 被称为公理化理论。
  ][
    WFF 之间存在有限个关系 $R_1^(j_1), R_2^(j_2), dots, R_n^(j_n)$，这里 $R_i^(j_i)$ 是一个判断规则，$j_i$ 是正整数，
    使得对任意 $j_i$ 个 WFF 和另一个 WFF $cal(B)$，都能在有限步内判断给定的 $j_i$ 个 WFF 和 $cal(B)$ 是否具有关系 $R_i^(j_i)$。
    如果有关系，我们说 $cal(B)$ 是这 $j_i$ 个 WFF 在关系 $R_i^(j_i)$ 下的结论。
    这些 $R_i^(j_i)$ 称为*推理规则(rules of inference)*。
  ]
]

#definition[
  $scr(S)$ 中的*证明*指的是有限长 WFF 序列 $cal(B)_1, dots, cal(B)_k$，并且对每个 $i$，$cal(B)_i$ 要么是公理，要么是它之前的
  WFF 在推理规则下的结论。

  $scr(S)$ 中的*定理*指的是一个 WFF $cal(B)$，并且是某个证明里最后一个 WFF，这样一个证明我们称为 $cal(B)$ 在 $scr(S)$ 中的证明。

  $scr(S)$ 称为*可判定的(decidable)*指的是对任意给定的 WFF 都能判断是否是 $scr(S)$ 中的一个定理；否则 $scr(S)$ 称为*不可判定理论*。

  一个 WFF $cal(C)$ 称为 WFF 集 $Gamma$ 的结论指的是存在 WFF 序列 $cal(B)_1, dots, cal(B)_k$ 使得 $cal(C) = cal(B)_k$，
  并且每个 $cal(B)_i$ 要么是公理，要么是 $Gamma$ 中的 WFF，要么是序列中排在前面的 WFF 在 $scr(S)$ 的推理规则下的结论。
  这样也序列称为从 $Gamma$ 到 $cal(C)$ 的证明。$Gamma$ 中的公式称为这个证明的假设或者前提。
  用 $Gamma tack.r cal(C)$ 表示 $cal(C)$ 是 $Gamma$ 的结论，如果为了避免歧义，可以用 $Gamma vdash_scr(S) cal(C)$。
  如果 $Gamma = {cal(B)_1, dots,cal(B)_k}$ 那么也可以写作 $cal(B)_1, dots,cal(B)_k vdash cal(C)$。
]

显然 $emptyset vdash cal(C)$ 当且仅当 $cal(C)$ 是定理。另外还有下面三个性质：
+ 如果 $Gamma subset Delta$ 以及 $Gamma vdash cal(C)$，那么 $Delta vdash cal(C)$。
+ $Gamma vdash cal(C)$ 当且仅当存在有限子集 $Delta subset Gamma$ 使得 $Gamma vdash cal(C)$。
+ 如果 $Delta vdash cal(C)$，并且 $Delta$ 中的每个公式都是 $Gamma$ 的结论，那么有 $Gamma vdash cal(C)$。

现在可以引入经典的命题演算理论 $scr(L)$ 了：
#enum[
  $scr(L)$ 的符号是 $not, ->, (, )$ 和字母 $A,B,C,dots$，以及用下标标记的字母 $A_1,A_2,dots$ 等，
  符号 $not, ->$ 称为*本源连接符(primitive connectives)*，字母称为陈述字母。
][
  - 所有陈述字母都是合式公式。
  - 如果 $cal(B), cal(C)$ 是合式公式，那么 $(not cal(B))$ 和 $(cal(B) -> cal(C))$ 是合式公式。
  所有的合式公式都可以通过上面规则构造出来。
][
  如果 $cal(B), cal(C), cal(D)$ 是合式公式，那么下列合式公式是公理（称为逻辑公理）：
  #enum(numbering: it => [(A#it)])[
    $(cal(B) -> (cal(C) -> cal(B)))$
  ][
    $( (cal(B) -> (cal(C) -> cal(D))) -> ( (cal(B) -> cal(C)) -> (cal(B) -> cal(D) ) ) )$
  ][
    $(((cal(not C)) -> (cal(not B))) -> ( ( (cal(not C)) -> cal(B) ) -> cal(C) ))$
  ]
][
  命题演算里唯一的推理规则是*肯定前件(modus ponens)*：$cal(C)$ 是 $cal(B)$ 和 $(cal(B) -> cal(C))$ 的结论。这条规则用 MP 来表示。
]

我们定义其他连接符：

#enum(numbering: it => [(D#it)])[
  $(cal(B) and cal(C))$ 定义为 $not( cal(B) -> not cal(C))$
][
  $(cal(B) or cal(C))$ 定义为 $(not cal(B)) -> cal(C)$
][
  $(cal(B) <-> cal(C))$ 定义为 $(cal(B) -> cal(C)) and (cal(C) -> cal(B))$
]

之后我们的公理理论至少包含上述命题逻辑。本笔记中的定理通常不给出证明，太繁琐了，具体参见@mendelson1997introduction。

#proposition[
  如果 $Gamma$ 是公式集，$cal(B), cal(C)$ 是公式。如果有 $Gamma, cal(B) tack.r cal(C)$，
  那么有 $Gamma tack.r cal(B) -> cal(C)$。
]

== 自然语言模型
本节用自然语言说明上述命题演算的一个模型，也就是给出一个语义。语义的精确定义是模型论的事情，本文不涉及。
所谓模型，就是一个让所有公理都为真的构造。

每个字母有两个取值，T 或者 F，表示真和假。$not$ 的真值表是：
#nonum-equation[$
            &A #h(2em) &not A \
            &"T" &"F" \
            &"F" &"T"
$]
而 $->$ 的真值表是：除了 $A$ 为 T，$B$ 为 F 时 $A -> B$ 为 F，其他都是 $T$。

通过这两个定义，可以递归得到每个公式的真值函数。如果公式始终为真，则这个公式称为*重言式(tautology)*，比如 $A or (not A)$。

不难验证，命题逻辑中的每个公理都是重言式。另外有：
#proposition[
  如果 $cal(B)$ 和 $cal(B) -> cal(C)$ 是重言式，则 $cal(C)$ 也是重言式。
]
于是
#proposition[
  命题演算中，每个定理都是重言式。
]
反过来，
#proposition(title: "完备性定理")[
  命题演算中的合式公式如果是重言式，则它是命题逻辑中的定理。
]
#corollary[
  命题演算是相容的，也就是不存在公式 $cal(B)$ 使得 $cal(B)$ 和 $not cal(B)$ 都是定理。
]

= 一阶逻辑
一阶逻辑同样有符号，字母，合式公式，推理规则，公理等概念。我们先介绍语法。

== 一阶理论
一阶逻辑的符号包括：括号 $()$，字母，命题逻辑的 $not,->$，全称量词 $forall$，还有下面四种符号：
- 变量：带下标的 $x$： $x_1, x_2, dots, x_n, dots$；
- 常量：带下标的 $a$：$a_1, a_2, dots, a_n, dots$；
- 谓词字母：$A_k^n$，这里 $n$ 和 $k$ 是正整数；
- 函数字母：$f_k^n$，这里 $n$ 和 $k$ 是正整数。
在谓词字母和函数字母中，上标 $n$ 表示参数的个数，下标用来区分有相同个数的参数的不同的函数或者谓词字母。
另外，为了方便，经常用 $x,y,z$ 等最后几个字母来表示变量 $x_1,x_2,x_3$。
经常用 $a,b,c$ 等前几个字母表示常量 $a_1, a_2, a_3$。

现在定义*项(term)*和*原子公式(atomic formula)*：
+ 变量和常量是项；
+ 如果 $f_k^n$ 是函数字母，$t_1,t_2,dots, t_n$ 是项，那么字符串 $f_k^n (t_1, dots, t_n)$ 也是项；
+ 所有的项都通过上面两个步骤得到。
把谓词应用在项上面得到原子公式，也就是说如果 $A_k^n$ 是谓词字母，$t_1, t_2, dots, t_n$ 是项，
那么字符串 $A_k^n (t_1,dots,t_n)$ 是原子公式。

#note-box[
  从语义上来说，谓词反映了项与项之间的关系或者具有的性质。而函数就是从一个项得到另一个项的办法。
]

于是我们合式公式定义为：
+ 原子公式是合式公式；
+ 如果 $cal(B), cal(C)$ 是合式公式，$y$ 是变量，那么 $(not cal(B)), (cal(B) -> cal(C))$ 和 $((forall y) cal(B))$ 是合式公式；
+ 所有合式公式都通过上面两个步骤得到。

在 $((forall y) cal(B))$ 当中，$cal(B)$ 称为量词 $(forall y)$ 的*作用域(scope)*。注意 $cal(B)$ 并不需要真的包含 $y$，
如果在这种情况，我们把 $((forall y) cal(B))$ 视为 $cal(B)$，可以当做一条推理规则。

表达式 $(cal(B) and cal(C)), (cal(B) or cal(C))$ 和 $(cal(B) <-> cal(C))$ 的定义与前面相同。
而存在量词 $exists$ 定义为全称量词的否定，也就是说
#nonum-equation[$
      ((exists x) cal(B)) "    表示    " (not((forall x)(not cal(B))))
$]

在通常的优先级约定下，可以省略括号，把括号的省略当做一条推理规则。

公式 $cal(B)$ 中的一个变量 $x$ 所占据的位置称为*约束占位(bound occurrence)*，
指的是 $x$ 出现在量词 $(forall x)$ 或者这个量词的作用域当中，
否则就说 $x$ 是*自由占位(free occurrence)*。

#example[
  + $A_1^2(x_1, x_2)$
  + $A_1^2(x_1, x_2) -> (forall x_1) A_1^1(x_1)$
  + $(forall x_1)( A_1^2(x_1,x_2) -> (forall x_1) A_1^1(x_1))$
  + $(exists x_1) A_1^2(x_1,x_2)$
  这里 1 当中的两个变量的占位都是自由的。2 当中第一个 $x_1$ 的占位是自由占位，第二个和第三个 $x_1$ 在约束占位里。
  3 当中所有的 $x_1$ 都在约束占位里。4 当中两个 $x_1$ 在约束占位中，注意 $exists$ 是 $forall$ 的否定。
]

一个变量 $x$ 称为*自由变量*或者*约束变量*指的是它在一个自由占位或者约束占位中。因此一个变量可能同时是自由变量和约束变量。

假设 $cal(B)$ 是公式，$t$ 是项，那么公式和项当中有多个变量，设 $x_i$ 是 $cal(B)$ 中出现的变量，$x_j$ 是 $t$ 中出现的变量。
如果量词 $(forall x_j)$ 的作用域当中如果没有自由变量 $x_i$，那么我们说 $t$ 对 $cal(B)$ 中的 $x_i$ 是自由的。

#example[
  #enum[
    项 $x_2$ 对 $A_1^1 (x_1)$ 中的 $x_1$ 是自由的，因为根本就没有量词；但是对 $(forall x_2)A_1^1 (x_1)$ 不是自由的。
  ][
    项 $f_1^2(x_1,x_3)$ 对 $(forall x_2) A_1^2(x_1,x_2) -> A_1^1(x_1)$ 的 $x_1$ 是自由的，因为量词里没有 $x_1,x_3$；
    但是对 $(exists x_3)(forall x_2) A_1^2(x_1, x_2) -> A_1^1(x_1)$ 的 $x_1$ 不是自由的，
    因为项里面的 $x_3$ 出现在公式的量词里面了。
  ] 
]

显然有：
+ 不包含变量的项对任何公式中的任何变量都是自由的。
+ 如果 $cal(B)$ 当中没有约束变量，则 $t$ 对 $cal(B)$ 中的每个变量都是自由的。
+ $x_i$ 对任意公式中的 $x_i$ 是自由的。
+ 如果 $x_i$ 在 $cal(B)$ 中都是约束变量，则任意项对 $cal(B)$ 中的 $x_i$ 都是自由的。


*一阶理论*是形式理论 $K$：
#enum[
  它的符号与合式公式在本节前面已经定义；
][
  它的公理除了命题演算里的三条逻辑公理，还有下面两条逻辑公理：
  #enum(start: 4, numbering: it => [(A#it)])[
    $(forall x_i)cal(B)(x_i) -> cal(B)(t)$，这里 $cal(B)(x_i)$ 是包含 $x_i$ 的公式，$t$ 是项，并且对 $x_i$ 自由。
    这里要求自由实际上是为了 $t$ 的变量和量词的变量互不干扰。
    注意 $t$ 可以是 $x_i$，于是 $(forall x_i)cal(B)(x_i) -> cal(B)$ 是公理。
  ][
    $(forall x_i)(cal(B) -> cal(C)) -> (cal(B) -> (forall x_i)cal(C))$ 这里 $cal(B)$ 不包含自由变量 $x_i$。
  ]

  以及*真公理(proper axioms)*：真公理随着理论的不同而不同，比如集合论中的 ZFC，群公理，实数公理等。如果一个理论没有真公理，
  则被称为*谓词演算(predicate calculus)*。
][
  它的推理规则除了前面命题演算里的肯定前件 MP以外，还有*一般化(generalization)*：$(forall x_i)cal(B)$ 是 $cal(B)$ 的结论。
]

#example(title: "一阶理论的例子")[
  #enum(numbering: "a.")[
    偏序结构：只有一个谓词 $A_1^2$，没有函数字母和常量。我们用 $x_1 < x_2$ 来代替 $A_1^2(x_1,x_2)$。这个理论具有两条真公理
    + 反反身性：$(forall x_1) not(x_1 < x_1)$
    + 传递性：$(forall x_1)(forall x_2)(forall x_3)(x_1 < x_2 and x_2 < x_3 -> x_1 < x_3)$
  ][
    群理论：有一个谓词 $A_1^2$, 一个函数 $f_1^2$，一个常量 $a_1$。我们用 $t =s$ 来替代 $A_1^2(t,s)$，用 $t dot s$ 来替代 $f_1^2(t,s)$，用 $1$ 来代替 $a_1$。
    这个理论有以下几条真公理：
    + 结合律：$(forall x_1)(forall x_2)(forall x_3)((x_1 dot x_2) dot x_3 = x_1 dot (x_2 dot x_3))$
    + 单位元：$(forall x_1)(1 dot x_1 = x_1 and x_1 dot 1 = x_1)$
    + 逆元：$(forall x_1)(exists x_2)(x_1 dot x_2 = 1 and x_2 dot x_1 = 1)$
    + 等号反身性：$(forall x_1)(x_1 = x_1)$
    + 等号对称性：$(forall x_1)(forall x_2)(x_1 = x_2 -> x_2 = x_1)$
    + 等号传递性：$(forall x_1)(forall x_2)(forall x_3)(x_1 = x_2 and x_2 = x_3 -> x_1 = x_3)$
    + 等号替代性：$(forall x_1)(forall x_2)(forall x_3)(x_2 = x_3 -> x_1 dot x_2 = x_1 dot x_3 and x_2 dot x_1 = x_3 dot x_1)$
  ]
  后面 4 条实际上是等号的性质，后面会介绍带等号的一阶理论，真正的群公理实际上只有前面 3 条。
]

== 一阶理论的模型
命题演算只需要通过真值表就能给出一个模型，但一阶理论要复杂一些。

#definition[
  *一阶语言* $scr(L)$ 包含了一阶理论所需的各种符号，也就是说它具有：
  + 命题演算连接符 $not, ->$ 和全称量词 $forall$。
  + 分隔符，也就是左括号 $($，右括号 $)$，还有逗号。
  + 至多可数多个变量 $x_1, x_2, dots$。
  + 至多可数个常量。
  + 至多可数个函数符号。
  + 至少一个谓词符号。

  $scr(L)$ 还要具有项，它根据前面的办法从 $scr(L)$ 的变量和常量以及函数符号得到。

  $scr(L)$ 还要具有合式公式，根据前面的办法从 $scr(L)$ 的原子公式还有命题连接符以及全称量词得到。
]

由合式公式的构成可以看出，如果没有谓词符号，则没有合式公式。从一阶语言的构成可以看出，它实质上是字符串集合，把某个一阶理论所需要的字符串都囊括进来了，
因此我们通常讨论一个一阶语言上的一阶理论，同一个一阶语言上可以有不同的一阶理论。
一阶语言给出了构建理论的材料，其上的一阶理论是使用这些材料的办法，即所谓材料之间的关系。而一阶语言的诠释，以及进而得到的一阶理论的模型，则给出了理论的含义。

#definition[
  设 $scr(L)$ 是一个一阶语言。它的一个*诠释(interpretation)*由下列部分组成：
  + 非空集合 $D$，称为*诠释域*。
  + 对每个谓词 $A_k^n$，指定一个 $D$ 上的 $n$-元关系 $(A_k^n)^M$，或者说是 $n$-元真值函数（也就是结果为 T 或者 F 的函数）。
  + 对每个函数 $f_k^n$，指定一个 $D$ 上的 $n$-元函数 $(f_k^n)^M$。
  + 对每个常量 $a_i$，指定一个 $D$ 中的元素 $(a_i)^M$。
]

在一个诠释下，就可以讨论一阶语言中的合式公式的真假了。没有自由变量的合式公式称为闭的，或者陈述，代表一个可能为真或者假的命题。
而有自由变量的公式，则可能对 $D$ 中某些元素为真，其他元素为假。

设 $M$ 是 $scr(L)$ 的一个诠释，$D$ 是诠释域。又设 $s$ 是 $D$ 中元素的一个序列 $s_1, s_2, dots$。
首先对 $scr(L)$ 中的项 $t$ 按如下方法指定一个 $D$ 中的元素 $s^*(t)$：
+ 如果 $t$ 是变量 $x_i$，那么 $s^*(t)$ 是 $s_i$。
+ 如果 $t$ 是常量 $a_i$，那么 $s^*(t)$ 是它的诠释 $(a_i)^M$。
+ 如果 $f_k^n$ 是函数，它对应 $D$ 上的 $n$-元函数 $(f_k^n)^M$，以及有项 $t_1, dots, t_n$，
则 $s^*(f_k^n (t_1, dots, t_n))$ 是 $(f_k^n)^M (s^*(t_1), dots, s^*(t_n))$。

因此递归地，每项都可以指定一个 $D$ 中的元素。直觉上来说，$s^*(t)$ 是把 $t$ 中的变量 $x_i$ 都替换为 $s_i$，
把常量 $a_i$ 替换为诠释 $(a_i)^M$，把函数替换为对应的 $n$-元函数然后进行演算得到的项。

现在我们可以做如下递归定义：
+ 若 $cal(B)$ 是原子公式 $A_k^n (t_1, dots, t_n)$，那么序列 $s$ *满足* $cal(B)$ 指的是 $(A_k^n)^M (s^*(t_1), dots, s^*(t_n))$，也就是 $n$-元组 $(s^*(t_1), dots, s^*(t_n))$ 有关系 $(A_k^n)^M$。
+ $s$ 满足 $not cal(B)$ 指的是 $s$ 不满足 $cal(B)$。
+ $s$ 满足 $cal(B) -> cal(C)$ 指的是 $s$ 不满足 $cal(B)$ 或者 $s$ 满足 $cal(C)$ （参考 $->$ 的真值表）。
+ $s$ 满足 $(forall x_i)cal(B)$ 指的是，对任意 $D$ 中的元素 $c$，序列 $s_1,s_2, dots, s_(i-1), c, s_(i+1), dots$ 都满足 $cal(B)$，也就是替换 $s$ 的第 $i$ 项为任意元素，都依然能满足 $cal(B)$。

直觉上来说，判断 $s$ 是否满足 $cal(B)$ 就是把其中的所有的自由变量 $x_i$ 相应替换为 $s_i$，然后用命题演算去判断是否为真。

#definition[
  + 一个公式 $cal(B)$ 对诠释 $M$ 为真，记作 $Vdash_M cal(B)$，指的是 $D$ 中任意序列都能满足 $cal(B)$。
  + $cal(B)$ 对 $M$ 为假指的是没有一个 $D$ 中序列能满足 $cal(B)$
  + 一个诠释 $M$ 称为公式集 $Gamma$ 的一个*模型(model)*指的是 $Gamma$ 中每一个公式都对 $M$ 为真。
]

下列性质很容易验证：
#proposition[
  设 $M$ 是诠释，$cal(B),cal(C)$ 是合式公式，则有
  #enum(numbering: "(I)")[
    - $cal(B)$ 对 $M$ 为假当且仅当 $not cal(B)$ 对 $M$ 为真。
    - $cal(B)$ 对 $M$ 为真当且仅当 $not cal(B)$ 对 $M$ 为假。
  ][
    不能同时有 $class("normal", tack.r.double)_M cal(B)$ 和 $class("normal", tack.r.double)_M not cal(B)$。
  ][
    如果有 $class("normal", tack.r.double)_M cal(B)$ 和 $class("normal", tack.r.double)_M cal(B) -> cal(C)$，
    那么就有 $class("normal", tack.r.double)_M cal(C)$。
  ][
    $cal(B) -> cal(C)$ 对 $M$ 为假当且仅当 $class("normal", tack.r.double)_M cal(B)$ 以及 $class("normal", tack.r.double)_M not cal(C)$。
  ][
    序列 $s$ 满足
    - $cal(B) and cal(C)$ 当且仅当 $s$ 满足 $cal(B)$ 和 $cal(C)$。
    - $cal(B) or cal(C)$ 当且仅当 $s$ 满足 $cal(B)$ 或者 $cal(C)$。
    - $cal(B) <-> cal(C)$ 当且仅当 $s$ 同时满足 $cal(B)$ 和 $cal(C)$ 或者同时不满足它们。
    - $(exists x_i) cal(B)$ 当且仅当有一个 $D$ 中的元素 $c$ 使得序列 $(s_1, dots, s_(i-1), c, s_(i+1),dots)$ 满足 $cal(B)$。
  ][
    $Vdash_M cal(B)$ 当且仅当 $Vdash_M (forall x_i)cal(B)$
  ]
]<诠释的性质>

接下来我们给出公式在语义上为真（而不是语法上可证明）的定义：
#definition[
  + 公式 $cal(B)$ 称为*逻辑有效的(logically valid)*指的是它对每个诠释都为真。
  + $cal(B)$ 称为*可满足的(satisfiable)*指的是存在一个诠释，其中至少有一个序列能满足 $cal(B)$。
  + $cal(B)$ 称为*矛盾的*指的是它对每个诠释都为假，也就是 $not cal(B)$ 是逻辑有效的。
  + 我们称 $cal(B)$ *逻辑推导出(logically imply)* 公式 $cal(C)$，记作 $cal(B) => cal(C)$ 指的是在每个诠释中，每个满足 $cal(B)$ 的序列都满足 $cal(C)$。更一般地，$cal(C)$ 是公式集 $Gamma$ 的逻辑结论指的是在每个诠释中，满足 $Gamma$ 中所有公式的序列也满足 $cal(C)$。
  + $cal(B)$ 和 $cal(C)$ 被称为*逻辑等价*指的是它们互相逻辑推到出对方，记作 $cal(B) <=> cal(C)$。
]


下列结论很容易验证：
+ $cal(B) => cal(C)$ 当且仅当 $cal(B) -> cal(C)$ 是逻辑有效的。
+ $cal(B) <=> cal(C)$ 当且仅当 $cal(B) <-> cal(C)$ 是逻辑有效的。
+ $cal(B) => cal(C)$ 以及 $cal(B)$ 对某个诠释为真，那么 $cal(C)$ 对这个诠释也为真。
+ $cal(C)$ 是公式集 $Gamma$ 的逻辑结论，$Gamma$ 中所有公式对给定诠释为真，则 $cal(C)$ 对这个诠释也为真。

#definition[
  设 $K$ 是一阶语言 $scr(L)$ 上的一个一阶理论。$K$ 的一个*模型*指的是 $scr(L)$ 的一个诠释使得 $K$ 的所有公理为真。
]

参考 @mendelson1997introduction，$K$ 任意定理对它的每个模型都为真。

#example(title: "群公理的模型")[
  诠释域 $D$ 取为整数集 $ZZ$，$=$ 是 $ZZ$ 的 $=$，$dot$ 是 $ZZ$ 里的 $+$，$1$ 取为 $ZZ$ 的 $0$。
  不难验证这个诠释是群公理的一个模型。
]

== 一阶理论的性质
同样，本节基本不会给出任何证明，具体参考 @mendelson1997introduction。同时从本节开始，用理论一词代替一阶理论。

#proposition[
  谓词演算的定理都逻辑有效。
]

#definition(title: "一致性")[
  一个理论被称为*一致的(consistent)*指的是其中不存在公式 $cal(B)$ 使得它和 $not cal(B)$ 都可证明（也就是都是定理）。
]

#note-box[
  考虑到一个公式和它的否定只能有一个对某诠释为真，因此只要一个理论有一个模型，那么这个理论就是一致的。
  因此一个常用的证明一致性的办法是找到模型，这实际上是把一致性问题往底层推。比如欧式几何公理的一致性可以由实数理论来保证。
]


上面的命题能推导出
#proposition[
  谓词演算是一致的。
]

== 带等号的一阶理论<等号公理>
设 $K$ 是一阶理论，且具有谓词 $A_1^2$。用 $t = s$ 来表示 $A_1^2(t,s)$，用 $t eq.not s$ 表示 $not A_1^2(t,s)$。
如果它还带有下列公理：
#enum(start : 6, numbering: it=> [(A#it)])[
  等号的反身性：$(forall x_1) x_1 = x_1$。
][
  等号的替换性：$(forall x)(forall y)x = y -> (cal(B)(x,x) -> cal(B)(x,y))$。
]
这里 $cal(B)(x,y)$ 表示替换部分（可以是也可以不是全部） $cal(B)(x,x)$ 中的占位符 $x$ 为 $y$。

显然前面给出的群理论是带等号的一阶理论。

#proposition[
  在任何带等号的理论中，有如下定理
  + 对任意项有 $t=t$，这是反身性
  + 对任意项 $t,s$ 有 $t=s -> s=t$，这是对称性。
  + 对任意项 $t,s,r$ 有 $t=s -> (s=r -> t=r)$，这是传递性。
]

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

= 宇宙

== Grothendieck 宇宙
Grothendieck 宇宙是 ZFC 中允许的一个集合 $cal(U)$，但它给出了 ZFC 的一个模型，在这个模型里可以用集合的方式来讨论集合以及真类。
它类似于运行在 ZFC 系统上的一台"虚拟机"，我们能在上面运行 ZFC，而对于太大的，无法用 ZFC 中合规的集合来表示的对象聚集，则表示为这个"虚拟机"外的集合，
因此它可以用宇宙之外的集合来这个宇宙的真类，这给了范畴论一个良好的基础，范畴论操作都可以在这个宇宙中进行，遇到需要表示"全体集合"的时候，就可以用这个 $cal(U)$。

#definition(title: "Grothendieck 宇宙")[
  *Grothendieck 宇宙(universe)*是一个集合 $cal(U)$，满足下列条件：
  + 传递性：对任意 $x in cal(U)$ 和 $y in x$ 有 $y in cal(U)$，即元素的元素还是元素，$in$ 关系具有传递性。
  + 二元集：如果 $x,y in cal(U)$，则 ${x, y} in cal(U)$。
  + 幂集：对任意 $x in cal(U)$，它的幂集 $"Pow"(x) in cal(U)$。
  + 如果 $(x_i)_(i in I)$ 是一族集合，每个集合 $x_i in cal(U)$ 以及指标集 $I in cal(U)$，那么 $union.big_(i in I) x_i in cal(U)$。
]
这个定义来自 @SGA4，其他作者有些会要求 $emptyset in cal(U)$ 或者 $NN in cal(U)$ 以排除较小的集合。$cal(U)$ 中的元素称为 $cal(U)$-集合，无歧义时简称为集合。

下列性质显然：
#proposition[
  - 如果 $x in cal(U)$ 则集合 ${x} in cal(U)$。
  - 如果 $x$ 是 $y in cal(U)$ 的子集，那么 $x in cal(U)$。
  - 如果 $x,y in cal(U)$，则二元组 $(x,y) = {{x,y},x} in cal(U)$。
  - 如果 $x,y in cal(U)$，那么并集 $x union y$ 和乘积 $x times y$ 都是 $cal(U)$ 的元素。特别地，所有 $cal(U)$ 中元素上的二元关系以及它们之间的函数都是 $cal(U)$ 的元素。
  - 如果 $(x_i)_(i in I)$ 是一族集合，每个集合 $x_i in cal(U)$ 以及指标集 $I in cal(U)$，那么 $product_(i in I) x_i in cal(U)$。
]<Grothendieck宇宙的基本性质>

#theorem[
  设 $cal(U)$ 是一个 Grothendieck 宇宙，且 $NN in cal(U)$，则 $cal(U)$ 是 ZFC 的一个模型。
]
#proof[
  设诠释域为 $cal(U)$。对谓词 $in$，指定 $cal(U)$ 上的关系 ${(x,y) in cal(U) times cal(U) | x in y}$，
  对谓词 $=$，指定 $cal(U)$ 上的关系 ${(x,y) in cal(U) times cal(U) | x = y}$。
  ZFC 里没有函数项和常数项，因此我们有了一个诠释 $M$。

  根据命题逻辑的真值表，很容易得到这个诠释满足逻辑公理 (A1) - (A3)。对于 (A4)，通过 @诠释的性质 可以看出，
  $Vdash_M (forall x_i) cal(B)(x_i)$ 时有 $Vdash_M cal(B)$。而对任意序列 $s$，因为 ZFC 没有常数项和函数项，因此
  $s^*(t)$ 必然是 $s_j$ 这种形式，$cal(B)(t)$ 必然是 $cal(B)(x_j)$ 这种形式，也就是把 $cal(B)$ 中的自由变元 $x_i$ 换成 $x_j$。
  但是 $Vdash_M cal(B)$ 可知，不论 $cal(B)$ 如何替换，它始终被任意序列满足，这样 (A4) 就为真了。

  (A5) 对 $M$ 为假当且仅当 $Vdash_M (forall x_i)(cal(B) -> cal(C))$ 以及 $Vdash_M not(cal(B) -> (forall x_i)cal(C))$。
  前者得到 $Vdash_M (cal(B) -> cal(C))$，后者得到 $Vdash_M cal(B)$ 以及 $Vdash_M not((forall x_i) cal(C))$。
  同样根据 @诠释的性质，就有 $Vdash_M cal(C)$，进而 $Vdash_M (forall x_i) cal(C)$，但是不能同时有 $Vdash_M not((forall x_i) cal(C))$，
  因此 (A5) 必然对 $M$ 为真。

  对于 @等号公理 的等号公理，显然是满足的，它直接继承了 $cal(U)$ 的集合论性质。

  而对于@外延公里 和@正规公理，结合 $cal(U)$ 的传递性就能验证。
  对于@分类公理，注意当 $A in cal(U)$ 时，分类公理得到的 $B$ 是 $A$ 的子集，因此通过 @Grothendieck宇宙的基本性质 可以验证。
  而 @配对公理，@并集公理，@幂集公理 直接来自 Grothendieck 宇宙的定义。
  @无穷公理 来自 $NN in cal(U)$。@选择公理 来自 $cal(U)$ 中集合族的选择函数存在性以及 @Grothendieck宇宙的基本性质。

  对于 @替换公理，若二元谓词 $cal(P)$ 满足对任意 $x in cal(U)$ 都有唯一 $y in cal(U)$，我们就可以定义函数
  $F : cal(U) -> cal(U)$ 使得 $F(x)$ 是唯一的 $y$ 使得 $cal(P)(x,y)$。
  这样对任意 $A in cal(U)$，通过替换公理得到的 $B$ 实际上可以表示为
  #nonum-equation[
    $ B := union.big_(x in A) {F(x)} $
  ]
  根据 Grothendieck 宇宙对索引并集的封闭性可以得到 $B cal(U)$。

  这样我们就证明了 $cal(U)$ 确实是 ZFC 的一个模型。
]

Grothendieck 宇宙提供了 ZFC 的一个模型，因此证明了它的一致性，而根据 Godel 第二不完备定理，ZFC 的一致性无法在 ZFC 当中证明，
这个宇宙又是在 ZFC 当中定义，因此我们有：
#corollary[
  Grothendieck 宇宙的存在性无法在 ZFC 当中得到证明。
]

因此 Grothendieck 提出了一条额外的公理来保证这种宇宙的存在：
#axiom(title: "宇宙公理")[
  对任意集合 $s$，都存在一个 Grothendieck 宇宙 $cal(U)$ 包含 $s$，也就是 $s in cal(U)$。
]

后面将证明每个 Grothendieck 都是一种 von Neumann 层级，反之亦然。
而 von Neumann 层级又是通过强不可达基数来定义的，因此不同的 Grothendieck 宇宙对应不同的不可达基数。

== von Neumann 宇宙