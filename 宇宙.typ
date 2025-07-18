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

基本性质：
#proposition[
  + 如果 $x in cal(U)$ 则集合 ${x} in cal(U)$。
  + 如果 $x$ 是 $y in cal(U)$ 的子集，那么 $x in cal(U)$。
  + 如果 $x in cal(U)$，则 $x$ 的商集 $y$ 是 $cal(U)$ 的元素。
  + 如果 $x,y in cal(U)$，则二元组 $(x,y) = {{x,y},x} in cal(U)$，更一般的多元组也是 $cal(U)$ 的元素。
  + 如果 $x,y in cal(U)$，那么并集 $x union y$ 和乘积 $x times y$ 都是 $cal(U)$ 的元素。
  + 所有 $cal(U)$ 中元素上的二元关系，两个元素之间的映射以及它们的集合都是 $cal(U)$ 的元素。
  + 如果 $(x_i)_(i in I)$ 是一族集合，每个集合 $x_i in cal(U)$ 以及指标集 $I in cal(U)$，那么乘积 $product_(i in I) x_i in cal(U)$ 和 不交并 $union.sq.big_(i in I) x_i in cal(U)$。
  + 任意个非空宇宙的交还是宇宙。
]<Grothendieck宇宙的基本性质>
#proof[
  这里只简要说明：2，根据定义可得 $"Pow"(x) in cal(U)$，因此从传递性可得 $y in cal(U)$。

  3，商集实际上是 $x$ 的划分，更具体说是一系列 $x$ 子集的集合，也就是 $"Pow"(x)$ 的子集，于是根据第 2 条就能得到。

  5，对任意集合 $x in cal(U)$，可得 $"Pow"(x)$ 进而 ${emptyset,x}$ 是 $cal(U)$ 的元素，因此 $2 in cal(U)$。于是两集合的并封闭。
  剩下的通过 ${x'} times y = union.big_(y' in y)(x',y') in cal(U)$，以及 $x times y = union.big_(x' in x){x'} times y$ 得到。

  6，$x,y$ 之间的二元关系实质是 $x times y in cal(U)$ 的一个子集；从 $x$ 到 $y$ 的映射是一种二元关系；
  而 $x$ 到 $y$ 的函数的集合是 $"Pow"(x times y)$ 的子集。

  7，不交并是 $union.big_(i in I) x_i times I in cal(U)$ 的一个子集，而乘积是一个从 $I$ 到 $union.big_(i in I) x_i$ 的映射。
]

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

  对于 @替换公理，若二元谓词 $cal(P)$ 满足对任意 $x in cal(U)$ 都有唯一 $y in cal(U)$ 使得 $cal(P)(x,y)$，我们就可以定义函数
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
#axiom(title: "Grothendieck 宇宙公理")[
  / (UA): 对任意集合 $s$，都存在一个 Grothendieck 宇宙 $cal(U)$ 使得 $s in cal(U)$。
]<Grothendieck宇宙公理>

后面将证明这个公理等价于不可达基数总是存在。

== 不可达基数
每个 Grothendieck 宇宙实际可以通过一个不可达基数来构造。在具体说明这个之前，先给出几个关于基数的结论。

#proposition[
  如果 $X subset cal(U)$ ，并且它的势不大于$cal(U)$ 中某个元素的势，那么 $X in cal(U)$。
]
#proof[
  假设 $abs(X) <= abs(J)$，这里 $J in cal(U)$。那么存在一个 $J$ 的子集 $I$ 和从 $I$ 到 $X$ 的双射 $i mapsto x_i$。
  那么显然有
  #nonum-equation[
    $ X = union.big_(i in I) {x_i} $
  ]
  然后根据 @Grothendieck宇宙的基本性质 可知 $I$ 和 $x_i$ 都是 $cal(U)$ 的元素，于是 $X in cal(U)$。
]

#corollary[
  如果 $cal(U)$ 非空，那么它的任意有限子集都是 $cal(U)$ 的元素，并且对任意有限基数 $cal(U)$ 都包含一个与之等势的集合。
]
#proof[
  设 $x_0 in cal(U)$，那么定义 $x_(n+1) = "Pow"(x_n)$，于是每个 $x_n in cal(U)$。考虑到 $abs(x_(n+1)) = 2^abs(x_n)$，
  因此 $cal(U)$ 含有与任意大有限基数等势的集合。
]

#definition(title: "正向集，共尾集，共尾类")[
  - *正向集(directed set)*是一个偏序集，其中任意两个元素都有上界。
  - 偏序集 $A$ 的*共尾子集(cofinal subset)*是一个子集 $B$ 使得对任意 $x in A$ 都存在 $y in B$ 满足 $x <= y$。
  - 偏序集 $A$ 的*共尾类(cofinality)*是 $A$ 的共尾子集的势当中的最小者，记为 $"cf"(A)$。
]

#example[
  - 一个集合的子集簇在包含关系下构成正向集，这里 $A <= B$ 定义为 $B subset.eq A$。任意全序集都是正向集。
  - 自然数集是实数集的一个共尾子集。自然数集的子集 $A$ 是是它的共尾子集当且仅当 $A$ 是无限子集。有最大元的偏序集的共尾子集必须包含这个最大元。
  - 显然自然数集的共尾类是 $aleph_0$，或者说 $aleph_0$ 的共尾类就是 $aleph_0$，因此 $aleph_0$ 是正规基数。
]

#definition(title: "正则基数")[
  无限基数 $kappa$ 如果满足 $"cf"(kappa) = kappa$，则称为*正则基数(regular cardinal)*，否则称为*奇异基数(singular cardinal)*。
]

#proposition(title: "等价定义")[
  设 $kappa$ 为基数，则下列命题等价：
  + $kappa$ 是正则基数
  + $kappa$ 不能写成少于 $kappa$ 个小于 $kappa$ 的基数和
  + 如果 $(alpha_i)_(i in I)$ 是一簇基数并且每个 $alpha_i < kappa$ 以及 $abs(I) < kappa$，那么 $sum_(i in I) alpha_i < kappa$
]<正则基数等价定义>
#proof[
  显然后两条等价。现在假设 $kappa$ 是正则基数，并且有一簇基数 $(alpha_i)_(i in I)$ 符合 3 的条件。
  给 $I$ 赋予良序，设 $I$ 和序数 $alpha$ 同构，并且把它们等同起来。于是我们就是要证明 $sum_(i in alpha) alpha_i < kappa$。
  对于 $beta <= alpha$，令 $f(beta) = sum_(i in beta) alpha_i$。假设 $f(alpha) < kappa$ 不成立，那么设 $beta$ 是最小的使得
  $f(beta) >= kappa$ 的序数。如果 $beta = beta' + 1$ 是后继序数，那么 $f(beta) = f(beta') + alpha_beta' >= kappa$，
  但是 $beta$ 的定义和 $alpha_beta'$ 的要求说明 $f(beta'), alpha_beta'$ 都小于 $kappa$，这和 @基数运算性质 矛盾。
  如果 $beta$ 是极限序数，也就是说 $beta = union.big_(delta < beta) delta$，此时由于每个 $f(delta)$ 是小于 $kappa$ 的序数，可以验证
  #nonum-equation[
    $f(beta) = union.big_(delta < beta) f(delta)$
  ]
  由于 $f(beta) >= kappa$，因此对任意序数 $gamma in kappa$，都存在 $delta < beta$ 使得 $gamma < f(delta)$，换句话说，集合
  ${f(delta)| delta < beta}$ 是 $kappa$ 的共尾子集，它的势 $|beta| <= |alpha| < kappa$，这与 $kappa$ 是正则基数矛盾。

  假设 $kappa$ 不是正则基数，那么取共尾类 $Z$，其序型为 $beta$，此时 $"cf"(kappa) = |beta| < kappa$。
  令 $f: beta -> Z$ 是同构，对于 $i in beta$，令
  #nonum-equation[
    $S_i = {x in kappa | x <= f(i) and forall j in i, f(j) < x}$
  ]
  于是 $kappa = union.big_(i in beta) S_i$ 并且还是不交并，同时我们也有 $|S_i| < kappa$，因此
  $alpha_i = |S_i|, i in beta$ 是不符合 2 的条件的一簇基数。
  #remark[
    这个 $S_i$ 的构造直观上是 $kappa$ 的一个右闭左开区间，右边是 $f(i)$。对任意 $x in S_i$，$f(i)$ 是 $Z$ 中大于等于 $x$ 的最小者。
    所以如果更一般的，我们知道 $Z = NN$ 是 $RR$的共尾子集，设 $beta$ 是自然数集，那么 $S_i = (i-1, i]$ 当 $i>0$，而
    $S_0 = (-infinity,0]$。

    显然对于 $i eq.not j$ 有 $S_i inter S_j = emptyset$。
  ]
]

#corollary[
  设 $kappa$ 为基数，则 $kappa^+$ 为正则基数。
]
实际上由 $kappa^2 = kappa$ 可得不超过 $kappa$ 个势不大于 $kappa$ 的基数之和不大于 $kappa$。

#definition(title: "不可达基数")[
  不可数基数 $kappa$ 称为*不可达基数(inaccessible cardinal)*，有时候会更精确地称为*强不可达基数*，指的是它满足：
  - $kappa$ 是正则基数
  - 对任意基数 $lambda < kappa$ 都有 $2^lambda < kappa$
]

#lemma[
  设 $A$ 是基数的集合，那么 $sup A$ 也是基数。
]
#proof[
  首先根据 @最小上界序数，$sup A$ 是序数。假设 $A$ 中有最大基数 $beta$，那么 $sup A = beta$ 还是基数。
  假设 $A$ 中没有最大基数，那么对任意小于 $sup A$ 的序数 $gamma$，都存在 $A$ 中的基数 $beta$ 满足 $gamma < beta < sup A$。
  此时 $gamma$ 不可能和 $sup A$ 建立双射，否则将有从 $beta$ 到 $gamma$ 的单射，
  结合原本从 $gamma$ 出发到 $beta$ 的单射以及 @CBS定理 就可以在 $beta$ 和 $gamma$ 之间建立双射，但 $beta$ 是基数，这是不可能的。
  因此 $sup A$ 是基数。
]

现在设 $cal(U)$ 是包含 $NN$ 的 Grothendieck 宇宙，那么 $x in cal(U)$ 是它的子集，因此 $abs(x) <= abs(cal(U))$。于是
${abs(x) : x in cal(U)}$ 是一个基数集合，这样就有基数：
#nonum-equation[
  $c(cal(U)) = sup_(x in cal(U)) abs(x)$
]
这个基数是不可数基数，更进一步还是不可达基数。首先，对任意小于它的基数 $lambda$，都存在一个 $x in cal(U)$ 并且 $abs(x) = lambda$；
实际上根据上确界的定义，肯定存在一个元素 $y in cal(U)$ 使得
#nonum-equation[
  $lambda <= abs(y) <= c(cal(U))$
]
因此 $lambda$ 必然和 $y$ 的某个子集 $x$ 等势，而 $x in cal(U)$ 根据 @Grothendieck宇宙的基本性质。
每个 $x in cal(U)$ 必然有 $"Pow"(x) in cal(U)$，所以
#nonum-equation[
  $abs(x) < 2^abs(x) = abs("Pow"(x)) <= c(cal(U))$
]
因此对任意小于 $c(cal(U))$ 的基数 $lambda$，可以取 $x in cal(U)$ 使其势为 $lambda$；而 $"Pow"(x) in cal(U)$ 于是
$abs("Pow"(x)) < c(cal(U))$，这样 $2^lambda < c(cal(U))$。

如果 $(alpha_i)_(i in I)$ 是小于 $c(cal(U))$ 的基数组成的集合，并且 $abs(I) < c(cal(U))$，那么根据上面的推理可以选择
$x_i in cal(U)$ 使得 $abs(x_i) = alpha_i$，以及某个 $cal(U)$ 中的与 $I$ 等势的，仍然记为 $I$ 的集合，用这个集合做指标集就有
#nonum-equation[
  $union.big.sq_(i in I) x_i in cal(U)$
]
这个元素的势就是 $sum_(i in I) alpha_i$，并且小于 $c(cal(U))$，因此 $c(cal(U))$ 是不可达基数。
也就是说 Grothendieck 宇宙的存在性蕴含不可达基数的存在性，并且 @Grothendieck宇宙公理[公理 (UA)] 蕴含
/ (UA'): 所有基数都严格小于一个不可达基数

反过来
#theorem[
  公理 (UA') 蕴含 Grothendieck 宇宙公理 (UA)
]
#proof[
  设 $A$ 是一个集合，我们将按照下面步骤构造一个拥有 $A$ 的 Grothendieck 宇宙 $cal(U)$。

  首先通过递归定义集合序列 $(A_n)_(n in NN)$：
  - $A_0 = A$
  - $A_(n+1) = A_n union union.big A_n$
  
  现在定义 $B = union.big_(n=0)^infinity A_n$，又设 $kappa$ 是大于 $|B|$ 的不可达基数。

  现在用超限递归定义一簇集合 $(B_alpha)_(alpha < kappa)$：
  $ B_0 &= B \
    B_(alpha + 1) &= B_alpha union "Pow"(B_alpha) \
    B_alpha &= union.big_(beta < alpha) B_beta "如果" alpha "是极限序数"
  $<B_alpha的定义>
  
  现在设 $cal(U) = union.big_(alpha < kappa) B_alpha$，我们将证明 $cal(U)$ 就是我们希望的 Grothendieck 宇宙。

  首先 $A in cal(U)$，这是因为 $A = A_0 subset B=B_0$，因此 $A in B_1 subset cal(U)$。

  现在我们证明对任意 $alpha < kappa$ 都有
  $ |B_alpha| < kappa $<B_alpha小于kappa>
  这可以通过超限归纳法证明：$|B_0| < kappa$ 是已知的。如果 $|B_alpha| < kappa$，那么根据 $kappa$ 是不可达基数就有
  $|B_(alpha + 1)| <= |B_alpha| + |"Pow"(B_alpha)| = |B_alpha| + 2^abs(B_alpha) <= kappa + kappa = kappa$。
  如果 $alpha$ 是极限序数，并且对任意 $beta < alpha$ 都有 $|B_beta|<kappa$，那么考虑到 $alpha < kappa$，于是根据 @正则基数等价定义 就有
  #nonum-equation[
    $|B_alpha| = abs(union.big_(beta in alpha) B_beta) <= sum_(beta in alpha) |B_beta| < kappa$
  ]
  这样就证明了 @B_alpha小于kappa。通过这个式子就可以证明对任意 $x in cal(U)$ 有
  $ |x| < kappa $<U元素小于kappa>

  我们将用超限归纳法证明对任意 $alpha < kappa$，$B_alpha$ 中元素的势小于 $kappa$。
  当 $alpha = 0$ 时，$x in B_0 = B$ 蕴含着存在正整数 $n$ 使得 $x in A_n$，于是 $x subset A_(n+1) subset B$，这样就有 $|x| <= |B| < kappa$。
  如果 $B_alpha$ 的元素的势小于 $kappa$，那么当 $x in B_(alpha + 1)$ 时有 $x in B_alpha$ 或者 $x subset B_alpha$，对于前者由归纳假设，对于后者由 @B_alpha小于kappa，都可得 $|x| < kappa$。
  如果 $alpha$ 是极限序数，并且对任意 $beta < alpha$，$B_beta$ 中元素的势都小于 $kappa$，则从 $x in B_alpha$ 得到 $x$ 属于某个
  $B_beta,beta < alpha$，于是 $|x| < kappa$。这样就证明了 @U元素小于kappa。

  现在可以验证 $cal(U)$ 满足 Grothendieck 宇宙的定义了：

  如果 $x in cal(U),y in x$，那么 $x$ 属于某个 $B_alpha$，我们用超限归纳法证明：对任意 $alpha < kappa$ 有断言
  #nonum-equation[
    $x in B_alpha and y in x --> y in B_alpha$
  ]
  当 $alpha = 0$ 时，$x in B_0$ 意味着存在正整数 $n$ 使得 $x in A_n$ 于是 $x subset A_(n+1)$，所以有 $y in B_0$。
  当 $alpha = beta + 1$ 并且对于 $beta$ 断言成立，则 $x in B_alpha$ 就有 $x in B_beta$ 或 $x subset B_beta$，对于前者采用归纳假设，
  对于后者直接有 $y in B_beta$，这样 $y in B_beta subset B_alpha$。而当 $alpha$ 是极限序数时，对 $alpha$ 断言可直接从归纳假设得到。
  因此 $cal(U)$ 是传递集。

  如果 $x,y in cal(U)$，则 $x,y$ 属于某个 $B_alpha$，这样 ${x,y} subset B_alpha$ 于是 ${x,y} in B_(alpha + 1) subset cal(U)$。

  如果 $x in cal(U)$，则 $x$ 属于某个 $B_alpha$，我们用超限归纳法证明：对任意 $alpha < kappa$ 有断言
  #nonum-equation[
    $x in B_alpha --> "Pow"(x) in B_(alpha + 2)$
  ]
  当 $alpha = 0$ 时，$x$ 属于某个 $A_n$，则 $x subset A_(n+1)$，故 $x$ 的子集 $y subset A_(n+1) subset B_0$，进而 $y in "Pow"(B_0) subset B_1$，
  也就是说 $"Pow"(x) subset B_1$，这样 $"Pow"(x) in B_2$。当 $alpha = beta + 1$ 时，如果断言对 $beta$ 成立，则
  $x in B_alpha$ 蕴含 $x in B_beta$ 或者 $x subset B_beta$，对于前者我们有 $"Pow"(x) in B_(beta + 2) = B_(alpha + 1) subset B_(alpha + 2)$，
  对于后者我们有 $"Pow"(x) subset "Pow"(B_beta) subset B_alpha$，所以 $"Pow"(x) in "Pow"(B_alpha) subset B_(alpha + 1) subset B_(alpha + 2)$。
  如果 $alpha$ 是极限序数并且断言对 $beta<alpha$ 都成立，则 $x in B_alpha$ 意味着存在 $beta < alpha$ 使得 $x in B_beta$，由归纳假设有
  $"Pow"(x) in B_(beta+2)$，注意到 $beta + 2 < alpha$ 因为 $alpha$ 是极限序数。这样就证明了 $cal(U)$ 对幂集运算封闭。

  设 $(x_i)_(i in I)$ 是一族 $cal(U)$ 中元素的集合，并且 $I in cal(U)$。每个 $x_i$ 都属于某个 $B_alpha$，
  可以选择一个函数 $alpha : I -> kappa$ 使得 $x_i in B_alpha(i)$。存在一个 $beta < kappa$ 使得对任意 $i in I$ 都有 $alpha(i) < beta$，否则
  #nonum-equation[
    $kappa = union.big_(i in I) (alpha(i) + 1)$
  ]
  注意到 $|alpha(i) + 1| < kappa$ 以及根据 @U元素小于kappa 有 $|I| < kappa$，这和 $kappa$ 是正则基数矛盾。现在根据 @B_alpha的定义
  可知 $B_alpha$ 随着 $alpha$ 的增大而扩大，于是对任意 $i in I$ 都有 $x_i in B_beta$。于是根据前面的证明有 $x_i subset B_beta$，这样有
  $x = union.big_(i in I) x_i subset B_beta$，所以 $x in B_(beta+1) subset cal(U)$，即 $cal(U)$ 对并集运算封闭。
]

== von Neumann 宇宙