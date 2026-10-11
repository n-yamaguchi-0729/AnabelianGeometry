# 双曲的曲線の Grothendieck 予想に向けた形式化計画

調査日：2026年9月30日（Asia/Tokyo）。対象：AnabelianGeometry。調査開始時の Git HEAD：8bbbe1ac7。Lean：4.35.0-rc2。mathlib：065356127b1dc0016f66b7283ce0ce2c4055aa55。

**推奨順序は、滑らかな固有複素曲線の解析化と GAGA、開曲線の Riemann 存在定理、算術基本群と惰性群の比較、重みを用いる復元、種数 0、一般アフィン曲線、固有曲線を含む一般の Isom 版である。** 群論・算術完全列の整備は解析の完成を待たず進められる。

本書は、最終定理の仕様、既存ライブラリの所在地、欠けている数学、実装順序を固定する。今回は計画とソースの静的調査のみであり、新しい Lean 定理の証明やライブラリ全体のビルドは行っていない。既存作業ツリーには多数の変更があるため、以下は HEAD だけでなく調査時の作業ツリーを見た記録である。「本文確認」は現 toolchain での検証済みを意味しない。

## 1 最終目標と定理の境界

### 1.1 最初に目指す一般定理

本計画では、まず k を Q 上有限生成な体、U と V を k 上の滑らかで幾何学的に連結な双曲的曲線とする。双曲性は、滑らかな固有化 X と幾何学的境界 D に対し、種数 g と穿孔数 r が 2g − 2 + r > 0 を満たすこととする。r = 0 も含める。

幾何点と k の分離閉包を整合的に選び、Π_U = π₁ᵉᵗ(U)、Δ_U = π₁ᵉᵗ(U_k̄) と書く。目標は自然な写像

\[
 \operatorname{Isom}_k(U,V)
 \longrightarrow
 \operatorname{Isom}^{\mathrm{cont}}_{G_k}(\Pi_U,\Pi_V)
 /\operatorname{Inn}(\Delta_V)
\]

の全単射性である。右辺は、G_k への射を保つ連続な群同型を、**標的の幾何学的核から来る共役**で割る。Π_V 全体の内部自己同型で割る定義にしない。基点やファイバー関手の同型の選択に依存しないことも、この自然写像の構成に含める。

これは Mochizuki の sub-p-adic 体上の定理の範囲に入る。最終的には sub-p-adic 体まで拡張するが、最初からその一般性をすべての基礎定義へ持ち込まない。[M99]

### 1.2 混同しない隣接目標

| 目標 | 本計画での扱い |
|---|---|
| weak Isom 版 | 群同型の存在から曲線同型の存在を得る中間成果。指定された群同型を復元する strong Isom 版とは別 |
| Hom 版 | 射の条件、開準同型、共役の扱いを改めて固定する後続課題 |
| section conjecture | 今回の最終目標には含めない。一般の切断を有理点と同定する仮定を途中で使わない |
| 正標数 | tame／幾何的 prime-to-p 商、Frobenius twist、非等定数性などを文献ごとに固定する別枝 |
| 絶対版 | G_k への構造射や基礎体の復元が加わる別課題 |
| 有限段可解版 | 段数を失う写像と、その像に入る同型を明示する。全段の群同型と同一視しない |

特に、幾何学的基本群だけでは標数 0 の曲線のモジュライは復元できない。複素比較で得る曲面群の表示は基礎であり、G_k 作用を含む算術的復元が別に必要である。[NTM]

## 2 現在のライブラリの地図

以下のリンクは本書からの相対パス。宣言の型や証明本文を確認したものと、候補の入口だけ確認したものを区別した。推移的な公理依存は未監査である。

| 必要な数学 | 現在の所在地と確認対象 | 再利用できる範囲と不足 |
|---|---|---|
| 固有滑らか曲線の構造射と基底変換 | [SmoothProperCurveBase.lean](../AlgebraicCurves/Geometry/Curves/SmoothProperCurveBase.lean)、[Models/Basic.lean](../AlgebraicCurves/Models/Basic.lean) | 本文確認。Scheme と SmoothOfRelativeDimension 1、IsProper を再利用。CurveModel は関数体・場所との対応まで持つので、任意の曲線に自動供給される型だとは扱わない |
| 関数体と場所 | [FunctionFields/CurveOver.lean](../AlgebraicCurves/FunctionFields/CurveOver.lean)、[Models/Construction.lean](../AlgebraicCurves/Models/Construction.lean)、[Models/Places.lean](../AlgebraicCurves/Models/Places.lean) | IsCurveOver は関数体側の条件。幾何学的連結性を含む Scheme 側の双曲曲線の定義そのものではない |
| 種数と Riemann–Roch | [Divisors/Canonical.lean](../AlgebraicCurves/Divisors/Canonical.lean)、[Cohomology/Adelic/Repartitions.lean](../AlgebraicCurves/Cohomology/Adelic/Repartitions.lean)、[Cohomology/RiemannRoch](../AlgebraicCurves/Cohomology/RiemannRoch) | genus と genusFF が存在。今回選ぶ Scheme の種数、基底変換後の種数、位相的種数との比較は別に確認・構成する |
| 有限 étale 被覆の圏 | [FiniteEtale/GaloisCategory.lean](../EtaleFundamentalGroups/FiniteEtale/GaloisCategory.lean)、[GeometricFiber/FundamentalGroup.lean](../EtaleFundamentalGroups/GeometricFiber/FundamentalGroup.lean) | fiberObjEquivHom、homEquivAlgHom、分離閉包上の IsFundamentalGroup の本文を確認。既存の fiber functor を使い、別の π₁ を作らない |
| 基本群の関手性と基点変更 | [GeometricFiber/Functoriality.lean](../EtaleFundamentalGroups/GeometricFiber/Functoriality.lean)、[BasePoint.lean](../EtaleFundamentalGroups/GeometricFiber/BasePoint.lean)、[FieldFundamentalGroupConjugacy.lean](../EtaleFundamentalGroups/GeometricFiber/FieldFundamentalGroupConjugacy.lean) | fundamentalGroupHom、fundamentalGroupIsoOfFiberIso、体の基本群写像との共役比較が入口 |
| 圏論的完全性判定 | [GaloisCategories/ExactSequence.lean](../EtaleFundamentalGroups/GaloisCategories/ExactSequence.lean) | autHomOfCompIso_exact_sequence_tfae の型を確認。核を像の閉正規包として記述する判定であり、幾何学的 π₁ の単射性と像の正規性まで自動では得ない |
| 被覆と開部分群 | [GeometricFiber/PointedCover.lean](../EtaleFundamentalGroups/GeometricFiber/PointedCover.lean)、[GaloisCovers](../EtaleFundamentalGroups/GaloisCovers) | fundamentalGroupEquivStabilizerOfLift 等が候補。曲線上の被覆の種数・境界・Galois 作用との整合を加える |
| 有限被覆の関数体 | [FiniteEtale/FunctionField.lean](../EtaleFundamentalGroups/FiniteEtale/FunctionField.lean)、[FunctionFieldNormalization.lean](../EtaleFundamentalGroups/FiniteEtale/FunctionFieldNormalization.lean) | finiteDimensional_functionField_of_finiteEtale_isConnected、isSeparable_functionField_of_finiteEtale_isConnected の宣言を確認。被覆圏と不分岐関数体拡大の圏同値の全体とは区別 |
| 局所惰性群と大域正規化 | [Inertia/AffineNormalizationGeometricPoint.lean](../EtaleFundamentalGroups/Inertia/AffineNormalizationGeometricPoint.lean)、[Inertia/ClosedNormalGeneration.lean](../EtaleFundamentalGroups/Inertia/ClosedNormalGeneration.lean) | 有限商での比較と閉正規包の一般論がある。選んだ cusp の局所 π₁ の像と大域 inertia の一致を完成させる必要がある |
| 局所 Kummer と分岐 | [EtaleFundamentalGroups/Kummer](../EtaleFundamentalGroups/Kummer)、[StrictHenselian](../EtaleFundamentalGroups/StrictHenselian)、[AbhyankarLemma](../SchemeTheory/AbhyankarLemma)、[ValuedFieldTheory](../ValuedFieldTheory) | 局所計算の再利用候補。高次元 purity 全体の完成を曲線の初期段階の前提にしない |
| プロ有限完備化と自由群 | [Completion/UniversalProperty.lean](../ProCGroups/Completion/UniversalProperty.lean)、[FreeProC](../ProCGroups/FreeProC)、[Presentations/Profinite.lean](../ProCGroups/Presentations/Profinite.lean)、[ReidemeisterSchreier](../ProCGroups/ReidemeisterSchreier) | IsProCCompletion、比較同型などを再利用。実際の曲線の π₁ がこの群に一致する証明は未確認 |
| 可換化と閉導来列 | [Abelian/TopologicalAbelianization.lean](../ProCGroups/Abelian/TopologicalAbelianization.lean)、[DerivedSeriesAndQuotients.lean](../ProCGroups/FiniteStepSolvableQuotients/Commutators/DerivedSeriesAndQuotients.lean) | topDerivedTop、MaxSolvQuot、連続全射との整合を再利用。算術群全体の可解商と幾何的可解商は別構成 |
| Fox 微分と関係加群 | [FoxDifferential](../ProCGroups/FoxDifferential)、[CrowellExactSequence/Profinite/MainTheorem.lean](../ProCGroups/CrowellExactSequence/Profinite/MainTheorem.lean) | profiniteSeparatedBlanchfieldLyndonLinearSequence_isExact 等を確認。Yamaguchi の自由可解群の中心化群計算に接続する候補 |
| ab-faithfulness と中心自明性 | [GroupTheory/Faithful.lean](../Yamaguchi26AbfaithfulGalois/GroupTheory/Faithful.lean)、[SlimnessAndTorsion.lean](../Yamaguchi26AbfaithfulGalois/GroupTheory/SlimnessAndTorsion.lean) | center_eq_bot_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful の本文確認。m ≥ 2、IsAbTorsionFree、IsAbFaithful を必要とする。これらを Δ_U について生成する幾何学が不足 |
| Picard と Jacobian | [JacobianVarieties/Picard](../JacobianVarieties/Picard)、[Pic0](../JacobianVarieties/Pic0)、[WeilPairing/Divisorial.lean](../JacobianVarieties/WeilPairing/Divisorial.lean) | Picard 表現可能性、因子、pairing の候補。実際の Jacobian の存在・Tate 加群・étale H₁ 比較まで完成とは認定しない |
| Galois cohomology と Kummer | [GaloisCohomology/Kummer](../GaloisCohomology/Kummer)、[ProfiniteIntegers](../GaloisCohomology/ProfiniteIntegers) | 係数・連続コホモロジーの候補。曲線の étale Kummer 列、Picard との比較、境界写像の自然性を別に作る |
| 類体論 | [ClassFieldTheory/README.md](../ClassFieldTheory/README.md)、[ArithmeticNormalization.lean](../ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean) | 具体的な大域相互法則は NumberField 仮定を持つ。有限体上の関数体の大域類体論へそのまま適用できない。一般論の再利用と関数体への具体化を分ける |

### 2.1 現状について特に注意する点

1. **AnabelianGeometry と EtaleFundamentalGroups/RiemannExistenceTheorem は調査時点で空。** 後者のディレクトリ名を完成定理の証拠にしない。
2. **ProCGroups/LocalWeight は位相の基・近傍基の最小濃度を扱う。** Nakamura の算術的 weight filtration とは異なる。今回必要な重み理論の既存実装には数えない。
3. **JacobianSchemeData は Jacobian の完成定理ではない。** [該当ファイル](../JacobianVarieties/Picard/JacobianSchemeData.lean)では hDim が単なる Prop のフィールドで、ofCore は True を代入している。種数と相対次元の一致をこの型から取り出すことはできない。実際の表現可能性・次元定理を供給する入口を別に固定する。
4. **ビルド履歴は現在の保証ではない。** [AC/JV RunState](../AlgebraicCurves/RunState.md)は2026年9月23日の中断記録で、[EFG BUILD_PROGRESS](../EtaleFundamentalGroups/BUILD_PROGRESS.md)は Lean 4.34 移行時の記録である。現 toolchain と変更済みソースの成功を示してはいない。
5. **Yamaguchi26SolvableCoverings は別論文の形式化。** [README](../Yamaguchi26SolvableCoverings/README.md)の題名は Extension of solvable coverings across horizontal divisors over the integers。今回再検索した 1.1、1.2、2.1、2.3 の証明には sorry が残る。既存の限定的な sorry 許容を AnabelianGeometry の主定理へ持ち込まない。

### 2.2 古い計画と現在のソースの対応

| 文書 | 引き継ぐ設計 | 今回の読み替え |
|---|---|---|
| [AC・JV抽出と曲線GAGA](../AC_JV_Extraction_and_Curve_GAGA.md) §5–6 | 有理型枠、局所有限ジェット、格子の貼り合わせ、Hom 比較、固有／開曲線 RET の順序 | これは重要な証明設計。しかし旧 Results/Proofs パスや旧 Arithmetic/GoodReduction の存在を現行実装と混同しない |
| [étale・惰性群の軽量計画](../etale_inertia_lightweight_formalization_plan.md) §0、8–9 | 次元1、有限商、境界惰性群の正規生成、算術完全列を段階化 | 現在は EFG の具体的なファイバー関手と体の基本群のソースがある。外部 pi1 の古い未完状況だけを根拠に再実装しない |
| [NC2 計画](../NC2_Section1_2_Formalization_Plan.md) §0 | 局所／大域 inertia 比較、purity の不足箇所を把握 | 記載された進捗率や許容 sorry はこの計画の完成度に転用しない。曲線で不要な高次元局所双対性を先行条件にしない |
| [Abfaithful の対応表](../Yamaguchi26AbfaithfulGalois/SOURCE_MAP.md) | 群論と絶対 Galois 群の応用の所在地 | 体の Galois 群での ab-faithfulness を曲線の幾何学的基本群へ無条件に転用しない |
| [SolvableCoverings 引継ぎ](../Yamaguchi26SolvableCoverings/HANDOFF.md) §主要な接続 | 局所群の像と正規化の固定部分群の比較がボトルネック | この比較の完成を確認して再利用する。下流の番号付き定理の存在だけを頼りにしない |

古い GAGA 計画が挙げる AlgebraicCurve.exists_eventuallyEq_evalAt_of_meromorphicAt は、現行 AC の解析部分には見つからない。Git 履歴では a9b530f28「refactor: remove complex analytic theorem campaign」が対応する削除である。読み取りで確認した既存アーカイブ [fermats-last-theorem-main.zip](../AlgebraicCurves/fermats-last-theorem-main.zip)には、二重の fermats-last-theorem-main ディレクトリの下に Theorems/Thm_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt.lean と P2M/Sol/S_AlgebraicCurve_exists_eventuallyEq_evalAt_of_meromorphicAt.lean がある。**回収候補であり、現在 import できる検証済みライブラリではない。** この ZIP は調査開始時から存在する未追跡ファイルなので、配布時の永続リンクとはしない。

回収時は、旧宣言が要求する複素多様体構造・コンパクト性・評価と位数の比較を誰が構成するかを確認する。外部由来コードの著作権、Authors、NOTICE、固定リビジョンとの対応を保持し、旧解析キャンペーン全体を復元しない。

## 3 GAGA をどこまで先に作るか

### 3.1 最初の解析的到達点

滑らかな**固有**連結複素曲線 X に対して、X の解析化、正則関数の層、解析的局所環、ベクトル束の解析化を構成する。smooth curve 全般の coherent GAGA を主張しない。A¹ の解析側の大域関数には exp(z) があり、代数側の C[z] と一致しない。[S56]

既存計画の存在版 GAGA を尊重する。ただし遠アーベル幾何での最小の出口は、有限局所自由な代数を代数化するための**任意有限階数のベクトル束の本質的全射性と Hom の全単射性**である。乗法・単位・結合律・被覆間の射も移すため、層の存在だけでは不足する。全 coherent sheaf の代数化は有用な後続到達点だが、全次数のコホモロジー比較を RET の必須前提にする必要はない。[SGA1]

| 段階 | 証明する内容 | 本質的な不足 |
|---|---|---|
| G0 | X(C) の複素曲線構造、正則関数層、Zariski 側との比較 | 旧解析化ソースの限定回収と現行 Scheme/Place の接続。コンパクト性・連結性を構成 |
| G1 | A = O_X,x → B = O_Xan,x、共通一様化元 t、A/(tⁿ) ≃ B/(tⁿ)、忠実平坦性 | 一変数正則関数の芽の DVR 性、代数的局所座標の解析的意味。A と B 自体の同一視はしない |
| G2 | 正則ベクトル束の大域有理型枠 | 主要な解析的未構成部分。解析的有限性・双対性、または別の独立した存在証明を要する |
| G3 | 局所格子の有限ジェットから代数的ベクトル束を貼り合わせる | 有限集合の外で標準格子、有限台商への射の核、解析化との整合 |
| G4 | 代数的ベクトル束間の Hom と解析的 Hom の比較 | 大域有理型関数の有理性、局所格子の正則性検出、射の一意性 |
| G5 | 一般 coherent sheaf の代数化存在と必要な Hom 比較 | 有限台 torsion と局所自由商、有限長局所加群、有限台 H¹ 消滅 |
| R0 | 有限位相被覆から一意な複素構造、有限解析的非分岐被覆との同値 | 被覆空間と複素局所座標の整合。単に両者を同じ型にしない |
| R1 | 固有 X 上の有限解析的非分岐被覆の代数化 | G3–G4 で q_*O を有限 O_X 代数にし、相対 Spec と étale 性の反映を構成 |
| R2 | U = X − D 上の有限位相被覆の代数化 | 境界の punctured disc 上で z ↦ zᵉ、有限被覆のコンパクト化、分岐射の代数化、U への制限 |
| R3 | 被覆圏の同値とファイバー関手の比較 | 対象の存在・射の全単射・基点との自然性をまとめ、π₁ᵉᵗ(U) ≃ 完備化 π₁top(Uan) を得る |

G2 の証明を「有理型枠を持つ」という構造体のフィールドにして先へ進めない。既存の代数的 Riemann–Roch を、まだ代数化されていない解析的ベクトル束へ適用するのも循環である。G3–G4 ができれば有限被覆に必要な部分を先に閉じ、G5 は並行して完成させられる。

R2 で代数化するコンパクト化の被覆は境界で分岐してよい。その場合も曲線間の有限射の押し出しが局所自由になることと、その代数構造を証明する。非固有 coherent GAGA へのすり替えは行わない。

### 3.2 代替案と選択

任意のコンパクト Riemann 面の代数化を解析的 Riemann–Roch から作り、写像の代数性と併せて直接 RET を証明する経路もある。これは固定した X 上の coherent GAGA と異なる定理で、解析的 Riemann–Roch 自体が必要である。**現状は既存計画との連続性から G0–G4 を第一候補とし、G2 の実証明の依存が見えた時点で比較する。** GAGA が Grothendieck 予想のあらゆる証明経路に論理的必須だという意味ではない。[S56, SGA1]

## 4 基本群と曲線の比較で必要なもの

### 4.1 幾何学的な比較

RET の後に必要なのは次の三段階である。

1. 有限被覆と有限連続 π₁ 集合を、同じファイバー関手を介して比較する。単なる抽象群同型では、境界のループと inertia の対応が失われる。
2. 複素曲線の位相的基本群について、種数 g、穿孔数 r の表示を証明する。

\[
 \langle a_1,b_1,\ldots,a_g,b_g,c_1,\ldots,c_r
 \mid \prod_{i=1}^{g}[a_i,b_i]\prod_{j=1}^{r}c_j=1\rangle.
\]

3. 代数的種数と位相的種数の一致、c_j の閉生成部分群と幾何的 inertia の一致、代数閉体拡大による有限被覆圏の不変性を証明する。これで標数 0 の一般の k̄ に戻す。

r > 0 の場合は一つの境界生成元を消去して自由プロ有限群の階数 2g + r − 1 を得る。r = 0 は曲面群であり自由群とはしない。三点除去直線の正規生成、二元による生成、自由性は別々の成果である。[N94, SGA1]

mathlib には [FundamentalGroupoid](../../.lake/packages/mathlib/Mathlib/AlgebraicTopology/FundamentalGroupoid)、[Topology/Covering](../../.lake/packages/mathlib/Mathlib/Topology/Covering)、[Analysis/Meromorphic](../../.lake/packages/mathlib/Mathlib/Analysis/Meromorphic) がある。これは一般基礎の入口であり、曲面分類・上の表示・種数比較の完成を確認したものではない。

### 4.2 算術完全列と外作用

目標は実際の構造射 U → Spec k から

\[
 1\longrightarrow\Delta_U\longrightarrow\Pi_U
 \longrightarrow G_k\longrightarrow1
\]

を構成すること。EFG の圏論的完全性判定に必要な有限被覆の降下・自明性判定を供給し、左の単射性、像の正規性、核との一致を別々に証明する。幾何学的群を定義上「構造射の核」にして、π₁(U_k̄) との比較を省略しない。

外作用 G_k → Out(Δ_U) はこの拡大から導く。U(k) の非空性や群拡大の分裂を仮定しない。最初は群拡大上の同型と幾何学的共役の商を使えば、巨大な Aut 群の位相の一般論を過度に先行させずに Isom 版を定式化できる。

幾何的 m 段可解商は

\[
 \Pi_U^{(m)}=\Pi_U/\Delta_U^{[m]},\qquad
 \Delta_U^{[0]}=\Delta_U,\quad
 \Delta_U^{[m+1]}=\overline{[\Delta_U^{[m]},\Delta_U^{[m]}]}.
\]

既存 MaxSolvQuot Π_U m をそのまま用いると G_k まで商を取るので誤り。幾何的 pro-Σ 版も、Π_U を Δ_U → Δ_U^Σ の核で割ってから扱う。[Y24, Y26]

### 4.3 境界の局所群

閉点 x ∈ D とその上の幾何点を選び、分解群 D_x、惰性群 I_x、残差 Galois 群への射を構成する。局所パラメータの Kummer 被覆から I_x の pro-ℓ 部分と Z_ℓ(1) を比較し、Galois 共役作用が円分指標となることを示す。ℓ は剰余標数と異なるものに制限する。

既存の ideal inertia、strict henselization の局所基本群、大域正規化の幾何点固定群は、名称が似ていても同じ定義ではない。有限 Galois 被覆ごとの比較を先に作り、逆極限で整合させる。分解群・惰性群の共役類、有限体拡大、被覆への制限、可解商への像をこの比較の出口にする。

## 5 Nakamura の weight filtration の実装目標

### 5.1 可換化における線形の重み

ℓ ≠ char(k)、U = X − D、r > 0 とする。構成する G_k 加群の完全列は

\[
0\to\mathbb Z_\ell(1)
\xrightarrow{\mathrm{diagonal}}
\mathbb Z[D(\bar k)]\otimes\mathbb Z_\ell(1)
\longrightarrow\Delta_U^{\mathrm{ab},\ell}
\longrightarrow T_\ell J_X\to0.
\]

境界項の像を W₋₂、全可換化を W₋₁ とし、W₋₃ = 0 とする。r = 0 では Δ_U^(ab,ℓ) ≃ T_ℓ J_X を別に扱う。穿孔数 r = 1 では境界項の像は零になり得るので、可換化だけで個々の inertia を検出できると考えない。[YS22, §1, (1)]

必要な供給元は、実際の Jacobian、有限段階のねじれと Tate 加群、étale Kummer 列、H₁ と可換化の比較、境界写像、被覆の pullback／norm の自然性である。一般化 Jacobian J_(X,D) を経由してもよいが、その表現可能性とトーラス部分も構成対象になる。既存の因子的 torsion の群を étale H¹ と呼び替えるだけでは完成しない。

重み −1 と −2 の区別には、有限体への良い還元、Frobenius 作用、曲線／Jacobian の Weil の評価が必要である。幾何的 Frobenius を用いれば T_ℓ J の固有値の絶対値は q^(-1/2)、Z_ℓ(1) は q^(-1) という規約にする。算術的 Frobenius を使う箇所は逆にする。Q_ℓ 上での固有値の分離から、Z_ℓ 格子の飽和性と積分的な W₋₂ の一致へ戻る工程も省かない。

### 5.2 非線形の重みと cusp 復元

Nakamura 1994 §2.1、Theorem (2.1.1) は、数体上の非固有双曲的曲線の幾何的 pro-C 基本群の非自明元 z について、**惰性群に属することを cyclotomic normalizer の存在で特徴づける**。C は同論文の full class の条件を満たすものとする。[N94]

定義を Lean に移す際には、Π の閉部分群 N が、z の閉生成部分群を正規化し、G_k への像が開で、N の共役作用がその G_k 像を通じて円分指標として作用することを明示する。「何らかの Galois 作用が円分的」という弱い条件にはしない。

この特徴づけが復元するのは、各 inertia の共役の合併である。一般には部分群ではなく、線形 W₋₂ や全境界の閉正規包とも異なる。証明では有限被覆上の可換化と重みの比較を繰り返す。したがって必要なのは U 一つの重み列だけでなく、有限被覆・開部分群に対する自然性である。

最初の出口は「G_k 同型が cusp inertia の共役類を保存する」であり、次に inertia の分離性・正規化群・分解群の対応へ進む。有限段可解商では元の定理をそのまま降ろさず、各論文の段数条件と復元可能な像を確認する。

### 5.3 非可換群上の重み列

pro-ℓ 幾何学的群の W₋₁ = Δ、W₋₂ = ker(Δ → T_ℓ J_X) から、交換子に適合する閉部分群列と付随次数 Lie 代数を作る課題もある。handle の次数を 1、cusp の次数を 2 とする規約を固定する。これは上の非線形特徴づけとは異なる。

この枝は具体的に使う復元定理が必要とする範囲から実装する。最初から混合 Hodge 構造、全導分 Lie 代数、配置空間の braid group 全体を完成させる必要はない。今回の最優先は 5.1 と 5.2 の接続である。

## 6 Yamaguchi の論文を使う順番

### 6.1 剛性を先に閉じる

[Y26] は中心自明性と有限段可解版の一意性に関する最も直接的な参考文献である。§1 では自由群の中心化群の旧証明に誤りがあることを指摘し、Proposition 1.3 で修正している。Fox 微分、Blanchfield–Lyndon 列、有限段可解商に関して既存 ProCGroups と重なるので、この修正版を基準にする。

一方、一般的な「IsAbTorsionFree と IsAbFaithful から m ≥ 2 の中心自明性」は既存ソースにある。新規の中心課題は、**Δ_U とその開部分群について両性質を生成すること**、そして曲線の自己同型の作用の忠実性・被覆の降下と結合して Isom 写像の単射性へ移すこと。中心が自明な群というだけでは任意の幾何学的函手の忠実性は従わない。

具体的な証明案は、RET と曲面群の表示から各連結有限被覆の可換化の torsion-freeness を得て、有限 deck 作用の忠実性を有理 ℓ 進 H₁ で検出することである。非自明な deck 変換が可換化上自明なら、その生成する有限巡回群の不変部分と中間被覆の H₁ を transfer により比較し、被覆次数に関する Euler 特性の乗法性と双曲性に矛盾させる。この経路には transfer／不変部分の比較と、有限被覆が実際の曲線の被覆として実現されることも要る。これらは今後証明する補題であり、既存の ab-faithfulness の仮定に隠さない。

### 6.2 種数 0 を最初の復元定理にする

[Y23] の種数 0・m ≥ 3 の経路と、[YS22] の解説を第一の復元キャンペーンにする。標数 0、境界が基礎体上で分裂する場合から始め、次いで有限 Galois 拡大による分裂と降下を証明する。境界に基礎体有理点がない種数 0 曲線を、最初から P¹_k と同一視しない。

実装する数学は、cusp／decomposition の復元、Kummer 類、差や cross-ratio の復元、PGL₂ の作用、配置の復元、関手性と Galois 降下である。四点の場合の λ の六つの変換に対する軌道は有用な小さい出口になるが、一般の四点 metabelian 版の証明と混同しない。

[YM26] は arXiv:2407.09906 **v2（2026年7月14日）**を基準に読む。題名は The metabelian Grothendieck conjecture for genus zero curves over finitely generated fields に改題されている。本文 Theorem A は標数 0 の有限生成体、g = 0、r ≥ 5 の weak 版を扱う。本文は r = 4 の一般の場合を未解決と記し、r = 3 は Proposition 6.6 で別扱いしている。abstract の広い表現から、すべての r ≥ 3 の metabelian 版を計画の完成目標として転記しない。

したがって「最小段数 2」への最適化より、まず段数 3 の範囲と full π₁ の種数 0 の Isom 版の関手性を堅く作る。段数 2 の r ≥ 5 はその後の独立した成果とする。

### 6.3 一般アフィン曲線

[Y24] の経路は、有限体上での分解群と関数体の復元、有限段可解 Oda–Tamagawa 良い還元判定、有限生成体への特殊化・降下である。確認した arXiv v1 の Theorem 0.8 では、weak 版の段数は r ≥ 3 かつ (g,r) ≠ (0,3),(0,4) で m ≥ 4、それ以外で m ≥ 5。strong 版は上位 m 段から下位 m−n 段へ降りる同型の**像**を対象とし、n ≥ 4、m > n を要求する。正標数では同定する圏と非等定数性の条件も加わる。[Y24, Theorem 0.8]

この経路を実装するには、有限体上の関数体の大域類体論、乗法群から加法を取り戻す補題、モデルの存在、特殊化の自然性が必要になる。数体向けの既存 CFT だけでここが閉じるとは見積もらない。完成済みの抽象類体論の供給条件を調べてから、関数体への適用を小さく分割する。

### 6.4 固有曲線を含む最終定理

一般アフィン版を完成しても、固有双曲的曲線で勝手に点を除くだけでは最終目標へ到達しない。群同型から、除く点や対応する開曲線の基本群を復元する cuspidalization 等が必要である。

一般 Isom 版の第一の典拠は [M99] とする。その証明に必要な p-adic Hodge 理論、微分・線束の復元、被覆による還元、降下は大きな未構成部分であり、GAGA と weight filtration の後に短い結合だけで終わるとは扱わない。

比較候補として [HY] も確認した。同論文の Corollary 11.3 は p-adic Hodge 理論を使わない経路を与えるが、log special fiber の復元、Prym-faithful な被覆、generalized Prym、Raynaud extension、Kummer-faithfulness 等が代わりに必要になる。現在のライブラリに近い部品だけで即座に完了する経路ではない。一般アフィン版までの再利用状況を見て、[M99] の証明依存と比較して選ぶ。

有限段から曲線の同型の存在を得ただけでは、最初に与えた full π₁ の同型を実現した証明にならない。全有限被覆との整合、必要な剛性、降下まで含めて最終の自然写像の全単射を示す。

## 7 AnabelianGeometry の配置案

以下は**提案する将来の配置**であり、現存ファイルの一覧ではない。今回作るのは本計画書のみ。

| ディレクトリ案 | 所有する内容 |
|---|---|
| Curves | compactified smooth curve、有限 étale 境界、種数・穿孔数、双曲性、基底変換 |
| AnalyticCurves | 曲線の解析化、正則関数層、局所環と一様化元。旧解析ソースの必要部分の回収先 |
| GAGA/Curves | LocalJets、MeromorphicFrame、VectorBundles、HomComparison、Coherent |
| Comparison | 有限位相／解析／étale 被覆の同値、ファイバー関手、複素比較、代数閉体拡大 |
| GeometricFundamentalGroup | 曲面群表示、自由群、境界ループ、種数比較 |
| ArithmeticFundamentalGroup | 算術完全列、幾何的商、G_k 同型の共役による同値関係 |
| Inertia | cusp と分解群、局所群の比較、円分作用、有限被覆と商の整合 |
| Weights | 可換化と Jacobian、境界の完全列、Frobenius、線形重み、非線形の特徴づけ |
| Rigidity | 幾何的 ab-faithfulness、ab-torsion-freeness、中心自明性、Isom の単射性 |
| Reconstruction/GenusZero | Kummer、cross-ratio、配置、種数0の復元と降下 |
| Reconstruction/Affine | 有限体、関数体、良い還元、特殊化、一般アフィン版 |
| Reconstruction/Proper | 選択した一般 Isom 版の証明、固有曲線の復元 |
| Grothendieck | 各定理の正確な公開 statement と、その実証明の統合 |
| Examples | P¹、G_m、三点除去直線、種数1の一穿孔、固有種数2以上 |

AC の現行 [LibraryScope](../AlgebraicCurves/LibraryScope.md) は解析キャンペーンを除外する方針なので、初期の解析/GAGA はこの依頼先の AnabelianGeometry 内に置く案とする。共通基礎として切り出す場合も、実装を伴う最小の単位だけを既存所有者へ移す。AnabelianGeometry を AC／JV の下位依存にして循環を作らない。

各 maintained ディレクトリには実ファイルを収録する All.lean を置き、ルートから再帰的に到達可能にする。leaf は必要な module を直接 import する。最初の実装時に Lake の独立ターゲットと集約を追加するが、今回は設定や空の Lean 足場を作らない。汎用群論は既存 ProCGroups、曲線論は AC、Picard/Jacobian は JV、有限被覆の一般論は EFG を優先して再利用する。

### 7.1 主要な依存関係

~~~mermaid
flowchart TD
  AC[既存の曲線論] --> AN[解析化と局所比較]
  AN --> GA[ベクトル束 GAGA と Hom 比較]
  GA --> RE[固有曲線と開曲線の Riemann 存在定理]
  RE --> GP[幾何学的基本群と曲面群の比較]
  PC[既存のプロ有限群論] --> GP
  EF[既存の有限 etale 被覆と Galois 圏] --> AP[算術完全列と幾何的商]
  EF --> IN[局所と大域の inertia 比較]
  GP --> RI[幾何学的剛性]
  PC --> RI
  JV[実際の Jacobian と Tate 加群] --> WT[境界完全列と線形重み]
  GP --> WT
  AP --> WT
  WT --> NW[非線形の重みと cusp 復元]
  IN --> NW
  NW --> GZ[種数0の復元]
  GZ --> AF[一般アフィン曲線の復元]
  FF[関数体 CFT と特殊化と良い還元] --> AF
  AF --> GC[全双曲的曲線の相対 Isom 版]
  PR[固有曲線を扱う追加の復元理論] --> GC
  RI --> GC
~~~

矢印は主要な必要工程を示す。種数0が一般アフィン版の全証明の必須定理だという主張や、各枝の詳細な import 閉包を表すものではない。

## 8 実装する順番と完了条件

| 順序 | まとまった成果 | 完了と判定する条件 |
|---|---|---|
| A0 | 曲線と標的の固定 | 実際の Scheme と境界の定義、双曲性、基点変更による共役の意味を固定。未証明の比較や復元を field に持たせない |
| A1 | G0 と G1 | 同一の曲線について解析化・正則関数層・局所環写像と有限ジェット比較を構成し、使用 leaf を検証 |
| A2 | G2–G4 | 有理型枠を実際に生成し、任意有限階数のベクトル束とその射を代数化 |
| A3 | R0–R3 | 非固有の場合も含む有限被覆圏の同値。乗法・射・ファイバー関手との整合を含む |
| A4 | 幾何学的表示 | 三点除去直線の自由群表示、次いで一般の種数と穿孔の表示。境界 inertia との一致と体拡大不変性も含む |
| A5 | 算術完全列と可解商 | G_k への実際の射、単射・全射・核、基点独立性、幾何的商の自然性を証明。A1–A4 と独立に進めてよい |
| A6 | 幾何学的剛性 | 幾何的群の全開部分群について必要な ab 条件を供給し、既存群論から中心自明性、さらに Isom の単射性へ接続 |
| A7 | 重みと cusp | 境界完全列と G_k 作用、Frobenius の重み分離、有限被覆の自然性、nonlinear characterization を実証明で閉じる |
| A8 | 種数0の Grothendieck 予想 | 分裂境界から一般境界への降下。weak 版と strong 版を区別し、指定された群同型との整合まで確認 |
| A9 | 一般アフィン版 | 有限体の復元・関数体 CFT・良い還元・特殊化を統合。各段数と正標数条件を保存 |
| A10 | 固有曲線を含む一般 Isom 版 | 選択した文献の追加の復元理論を完成し、1.1 の自然写像の全単射性を証明 |

### 8.1 最初の実装バッチ

**現在の最初の未完了箇所は A0–A1。GAGA の完成定理を直ちに書く段階ではない。** 次の順で、小さい実構成から始める。

1. Curves/Basic：構造射が滑らか・固有・幾何学的連結な X と有限 étale な閉境界 D、開補集合 U を実際に定義する。CurveModel が必要になる箇所だけで既存の構成定理から作る。
2. Curves/Boundary：境界の幾何点の有限性と穿孔数の体拡大不変性。種数の既存二定義との比較を別補題にする。
3. Curves/Hyperbolic：自然数の切り捨て減算による誤定義を避け、2 < 2g + r または整数上の不等式で双曲性を定義する。P¹ と G_m は非双曲、三点除去直線は双曲であることを確認する。
4. AnalyticCurves/Structure：旧解析化の実証明と依存を限定して読み、現行 Scheme/Place と正則関数層の接続を作る。初期の具体例は P¹_C とその標準アフィン座標とする。
5. GAGA/Curves/LocalJets：正則芽の環と代数的局所環の写像、共通一様化元、有限ジェット比較を構成する。解析的局所環を「DVR で有限ジェット同型がある環」という仮定付き代用品にしない。
6. 独立した小バッチとして、EFG の既存ファイバー関手から曲線同型が誘導する外部群同型の自然写像を作る。その後、算術完全列に必要な有限被覆の降下を最小の不足補題まで分ける。

G2 が詰まった場合、任意束の有理型枠を仮定して上位の theorem を作るのではなく、解析的 H⁰ の有限性や線束の非零有理型切断など、実際に供給できる最小の定理へ戻る。

## 9 検証と進捗の記録

実装時の各公開定理には、数学的仮定、既存の供給元、未構成の最小事実、確認した leaf と公理依存を対応づける。宣言が存在すること、証明本文があること、build 成功、推移的に sorryAx がないことを別々に記録する。

- 新規 sorry／axiom や、結論・核心的比較を仮定に移した構造体を作らない。
- 変更した leaf を直接指定して検証し、必要な consumer と最小 aggregate へ広げる。文書だけの変更のために全体 build は走らせない。
- 節目では公開定理の公理依存を確認する。既存の限定許容 sorry が import 閉包に入る場合、最終定理の完成とは数えない。
- `.olean` の存在だけを現ソースの成功の証拠にしない。実行中の別作業による依存ソース変更にも注意する。
- 検証例は仮定の境界を検出するものにする。r = 0 と r = 1、g = 0、非分裂境界、基点変更、有限体拡大、m = 1 と m ≥ 2 を区別する。
- 本計画は根拠のない達成率や所要日数を付けない。依存定理が実際に閉じた時に該当段階を更新する。

今回の検証は、参照ファイルの実在、選択した宣言・仮定、旧計画との差、論文の該当定理、文書のリンクと差分の確認に限る。Lean ソース・Lake 設定・依存ライブラリは変更していない。

## 10 文献と参照箇所

URL は2026年9月30日に検索・確認。数値条件は abstract より本文の定理を優先する。以下の実装順序と配置案は本書の提案であり、各文献が Lean 実装の存在を保証するものではない。

| 略号 | 文献と参照箇所 | この計画での用途 |
|---|---|---|
| S56 | J.-P. Serre, [Géométrie algébrique et géométrie analytique](https://numdam.org/articles/10.5802/aif.59/), Ann. Inst. Fourier 6 (1956), 1–42 | 固有／射影の場合の GAGA の原典。曲線への制限と実装経路は既存ローカル計画 §5–6 と比較 |
| SGA1 | A. Grothendieck, M. Raynaud, [Revêtements étales et groupe fondamental](https://arxiv.org/abs/math/0206203), Exposé XII, Théorème 5.1 | 有限 étale 被覆の解析比較。説明には [Milne, Lectures on Étale Cohomology, Theorem 21.3](https://www.jmilne.org/math/CourseNotes/LECc.pdf)も参照 |
| N90a | H. Nakamura, Rigidity of the arithmetic fundamental group of a punctured projective line, J. reine angew. Math. 405 (1990), 117–130 | 重みと Kummer による四点配置の復元。[出版社の巻目次](https://www.degruyterbrill.com/journal/key/crll/1990/405/html)。詳細は YS22 §1 で確認し、原論文の全証明は今回未精査 |
| N90b | H. Nakamura, Galois rigidity of the étale fundamental groups of punctured projective lines, J. reine angew. Math. 411 (1990), 205–216 | 種数0の歴史的基準。書誌と位置づけは N94 §2.1、YS22 §3・参考文献で確認。原論文本文の直接精査は後続 |
| N94 | H. Nakamura, [Galois rigidity of pure sphere braid groups and profinite calculus](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms010103.pdf), J. Math. Sci. Univ. Tokyo 1 (1994), 71–136, §2.1、Theorem (2.1.1) | nonlinear weight filtration。印刷頁93–97を参照し、特に頁94の定義と定理を画像でも確認 |
| YS22 | N. Yamaguchi, [A survey of known results on the m-step solvable anabelian geometry for hyperbolic curves](https://arxiv.org/abs/2204.08008), §1–3 | 線形重みの完全列、Nakamura の方法、Mochizuki と種数0の方法の比較。頁3の完全列を画像でも確認 |
| Y23 | N. Yamaguchi, [The geometrically m-step solvable Grothendieck conjecture for genus 0 curves over finitely generated fields](https://arxiv.org/abs/2010.00290), J. Algebra 629 (2023), 191–226 | 種数0の有限段可解版。Theorem 2.4.1 の位置づけ・仮定は Y24 Theorem 0.6 と YS22 も照合。実装前に採用する本文の版を固定 |
| Y24 | N. Yamaguchi, [The geometrically m-step solvable Grothendieck conjecture for affine hyperbolic curves over finitely generated fields](https://arxiv.org/html/2302.09253v1), JLMS 109 (2024), e12912 | 今回は arXiv v1 の Theorems 0.7–0.9 と証明概略を確認。§2 有限体、§3 良い還元、§4 有限生成体。刊行版との番号・仮定の最終照合は実装時に行う |
| YM26 | N. Yamaguchi, [The metabelian Grothendieck conjecture for genus zero curves over finitely generated fields](https://arxiv.org/html/2407.09906v2), v2, 2026-07-14, Theorem A、Remark 3.9、Proposition 6.6 | r ≥ 5 の改良、r = 4 の制約、r = 3 の別扱い。旧題名・旧 abstract だけで対象を広げない |
| Y26 | N. Yamaguchi, [Center-freeness of finite-step solvable groups arising from anabelian geometry](https://arxiv.org/html/2601.07112v1), Theorems A–B、Proposition 1.3、Theorem 2.9 | 中心自明性・中心化群の修正・剛性。URL の版表示は v1、取得本文内の日付は2026年8月24日であり、実装時には本文スナップショットも固定 |
| T97 | A. Tamagawa, [The Grothendieck conjecture for affine curves](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/1992BA14A2D63FA076DB39A34EC45E83/S0010437X97000614a.pdf/div-class-title-the-grothendieck-conjecture-for-affine-curves-div.pdf), Compositio Math. 109 (1997), 135–194 | Y24 が用いる一般アフィン版の基礎。今回の証明経路の要約は Y24 の参照箇所に基づく |
| M99 | S. Mochizuki, [The Local Pro-p Anabelian Geometry of Curves](https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Local%20Pro-p%20Anabelian%20Geometry%20of%20Curves.pdf), Invent. Math. 138 (1999), 319–423, Theorem A、§15–18 | 一般の sub-p-adic 体上の目標。有限段からの復元では Theorem 18.1 の段数差も確認する |
| HY | Y. Hoshi, Y. Yang, [The arithmetic fundamental groups of curves over local fields](https://www.kurims.kyoto-u.ac.jp/~yuyang/papersandpreprints/FGLF.pdf), Introduction、§1–11、Corollary 11.3 | 一般 Isom 版の代替経路。取得本文の導入・必要理論を確認。採用する場合は版と全依存定理を改めて固定 |
| NTM | H. Nakamura, A. Tamagawa, S. Mochizuki, [The Grothendieck conjecture on the fundamental groups of algebraic curves](https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Grothendieck%20Conjecture%20on%20the%20Fundamental%20Groups%20of%20Algebraic%20Curves.pdf), Sugaku Expositions 14 (2001), 31–53 | 相対算術基本群からの復元と古典的結果の全体像 |

Yamaguchi の [論文一覧](https://n-yamaguchi-0729.github.io/homepage-en)から、算術曲面上の相対版や Deligne–Mumford 曲線への発展も確認できる。今回の一般曲線の基礎には、それらの追加の対象を先行条件として含めない。


## 2026-10-09: 明示的に依頼された標数0の表示

深さ3のライブラリとして登録した。`GeometricFundamentalGroup/CharZeroPresentation.lean` に、代数閉体・標数0上の滑らかな曲線の実エタール基本群のprofinite表示を置く。`exists_surfacePresentation_charZero` の証明の `sorry` 1個だけをユーザーが明示許可した。inertiaによる固有化基本群の商の同定は依頼に従い含めない。これは証明済みの進捗ではなく、定理statementの形式化である。以前の計画の一般的なsorry禁止に対する例外はこの宣言だけ。
