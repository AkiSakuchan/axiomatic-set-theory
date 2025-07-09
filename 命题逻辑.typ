#import "book-style.typ": *
#import "@preview/theorion:0.3.3": *
#import "@preview/commute:0.3.0": node, arr, commutative-diagram
#import cosmos.rainbow: *
#show: show-theorion

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