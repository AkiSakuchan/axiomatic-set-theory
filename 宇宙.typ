#import "book-style.typ": *
#import "@preview/theorion:0.3.3": *
#import "@preview/commute:0.3.0": node, arr, commutative-diagram
#import cosmos.rainbow: *
#show: show-theorion

#let vdash = math.class("normal", math.tack.r)
#let Vdash = math.class("normal", math.tack.r.double)

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
  而@配对公理，@并集公理，@幂集公理 直接来自 Grothendieck 宇宙的定义。
  @无穷公理 来自 $NN in cal(U)$。@选择公理 来自 $cal(U)$ 中集合族的选择函数存在性以及 @Grothendieck宇宙的基本性质。

  对于 @替换公理，若二元谓词 $cal(P)$ 满足对任意 $x in cal(U)$ 都有唯一 $y in cal(U)$，我们就可以定义函数
  $F : cal(U) -> cal(U)$ 使得 $F(x)$ 是唯一的 $y$ 使得 $cal(P)(x,y)$。
  这样对任意 $A in cal(U)$，通过替换公理得到的 $B$ 实际上可以表示为
  #nonum-equation[
    $ B := union.big_(x in A) {F(x)} $
  ]
  根据 Grothendieck 宇宙对索引并集的封闭性可以得到 $B in cal(U)$。

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