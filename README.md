# AnabelianGeometry

[![Lean](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml/badge.svg)](https://github.com/n-yamaguchi-0729/AnabelianGeometry/actions/workflows/lean.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

**開発途中の Lean 4 ライブラリです。目的は双曲的曲線に対する Grothendieck 予想の形式化であり、その最終定理はまだ証明していません。**

## 目標

まず標数0の有限生成体 `k` 上の滑らかな幾何学的連結双曲曲線 `U, V` について、曲線の `k`-同型と、絶対 Galois 群 `G_k` への構造射を保つ連続な算術エタール基本群同型との対応を構成し、その全単射性を証明することを目指します。基本群同型の側は、標的の**幾何学的核**による内部共役で割ります。指定された群同型を幾何的に復元する strong Isom 版が目標です。

詳細は [形式化計画](Lean4/AnabelianGeometry/PLAN.md) を参照してください。同計画の2026年9月30日の調査部分には「ソースが空」などの当時の記録も残っています。現在の実装状況は以下とリンク先の現行ソースを優先してください。Hom 版、section conjecture、正標数での一般形は、この最初の完成目標に含めていません。

## 現在の実装

`AnabelianGeometry` 本体は44個の Lean モジュールです。群は実際の有限エタール被覆の幾何的ファイバー関手の自己同型群として扱います。以下の結果はそれぞれのソースに明示された曲線モデル・体・基点などの仮定の下の定理です。

| 内容 | 宣言・ソース | 範囲 |
|---|---|---|
| 固有双曲曲線の基本群の slimness | [`isSlim_fundamentalGroup_proper_hyperbolic`](Lean4/AnabelianGeometry/GeometricFundamentalGroup/ProperCurveSlim.lean) | 代数閉体・標数0、`[IsCurveOver K F]`、`CurveModel K F` と `2 ≤ genusFF K F`。実際の開部分群を連結有限エタール被覆で実現し、被覆の種数と deck 変換の H¹ 作用を使う。 |
| 開双曲曲線の基本群の slimness | [`isSlim_fundamentalGroup_open_hyperbolic`](Lean4/AnabelianGeometry/GeometricFundamentalGroup/OpenCurveSlim.lean) | 代数閉体・標数0、固有曲線モデルへの準コンパクト・準分離な開埋め込み。始域は整・正規・局所 Noether・準コンパクト、境界は非空、`2g + r - 2 > 0` は整数上の不等式。境界の有限性はモデルから供給する。非正規な開部分群も含む。 |
| 固有種数0曲線の基本群の自明性 | [`subsingleton_fundamentalGroup_of_genus_zero`](Lean4/AnabelianGeometry/GeometricFundamentalGroup/GenusZeroFundamentalGroup.lean) と [coherent H¹による定式化](Lean4/AnabelianGeometry/GeometricFundamentalGroup/ProperGenusZero.lean) | 代数閉体・標数0。後者は滑らかな固有整曲線と二アフィン開被覆を入力とし、構造層 H¹ の次元が0なら任意の幾何点で基本群が自明であることを示す。 |
| アフィン直線と一穿孔の場合 | [`subsingleton_fundamentalGroup_affineLine`](Lean4/AnabelianGeometry/GeometricFundamentalGroup/AffineLineFundamentalGroup.lean)、[一穿孔曲線](Lean4/AnabelianGeometry/GeometricFundamentalGroup/OnePunctureGenusZero.lean) | 代数閉体・標数0。アフィン直線の連結有限エタール被覆は同型。一穿孔版は滑らかな固有整曲線の構造層 H¹ の次元が0で、指定した閉点の補集合である場合を扱う。 |
| 二穿孔種数0曲線 | [二穿孔曲線の基本群](Lean4/AnabelianGeometry/GeometricFundamentalGroup/TwoPuncturesFundamentalGroup.lean) | 代数閉体・標数0。滑らかな固有整曲線の構造層 H¹ の次元が0で、相異なる二閉点の補集合である場合、任意の幾何点で全 profinite integers との位相群同型と位相的生成元を構成する。Laurent/Kummer 被覆と任意の正整数位数の有限商を使う。 |
| 被覆・作用・コホモロジーの基礎 | [固有曲線の deck 忠実性](Lean4/AnabelianGeometry/GeometricFundamentalGroup/ProperDeckFaithfulness.lean)、[開曲線の deck 忠実性](Lean4/AnabelianGeometry/GeometricFundamentalGroup/OpenDeckFaithfulness.lean) | 有限係数 H¹、被覆の固有化、Riemann–Hurwitz の幾何的計算を slimness に接続する。 |

[`IsSlim`](Lean4/ProCGroups/FiniteStepSolvableQuotients/SlimnessAndTorsion.lean) は、すべての開部分群 `H` の**周囲の群における中心化群**が自明であるという条件です。上の2つの主定理はこの既存の群論的述語を結論にしています。幾何点はいずれも分離閉体上のものを許します。これらは Grothendieck 予想へ向けた幾何的基礎であり、算術基本群から曲線を復元する最終定理ではありません。

上の slimness と種数0の基本群計算は、次の未証明の曲面表示を使わずに構成されています。各主定理のローカル import 閉包にも `CharZeroPresentation` は含まれません。なお、[二穿孔補集合と Laurent 多項式環のスペクトルとの幾何的同型](Lean4/AnabelianGeometry/GeometricFundamentalGroup/TwoPuncturesGenusZero.lean) 自体には標数0の仮定がありませんが、ここで述べた全エタール基本群と profinite integers の同型には標数0が必要です。

## 明示的な未証明定理

[`AnabelianGeometry.GeometricFundamentalGroup.exists_surfacePresentation_charZero`](Lean4/AnabelianGeometry/GeometricFundamentalGroup/CharZeroPresentation.lean) は、2026年10月9日に明示的に許可された **`sorry` 1個を含む未証明定理**です。

代数閉体・標数0上の滑らかな固有整曲線から有限個の点を除いた曲線について、ハンドル生成元・境界 inertia 生成元と曲面関係式による profinite 表示を定式化しています。種数は実際の二アフィン開被覆の構造層 H¹ の次元から定め、境界 inertia も局所環の整閉包の inertia の像として定義しています。双曲性は仮定せず、境界が空の場合や inertia の像が自明になる低種数の場合も含む statement です。

このファイルは定理の statement の形式化です。証明済みの成果には数えず、CI でもこの警告を表示して「未証明」と報告します。境界 inertia の閉正規包で割った商と固有化の基本群との同定は、この許可の対象にも定理の主張にも含みません。

## 今後必要な構成

- 上記の曲面表示の証明を、曲線の解析比較・Riemann 存在定理等から構成する。
- 算術基本群、幾何的核、境界 inertia の必要な比較・自然性を揃える。
- 群と Galois 作用から境界・曲線の幾何を復元し、体・曲線同型を構成する。
- 指定された基本群同型との整合、共役による同値関係、自然写像の全単射性を証明する。

これらを未証明の入力に置き換えて Grothendieck 予想の完成とは扱いません。

## 依存関係を含む配布範囲

各行のライブラリの **全 maintained source** を収録しています。主ライブラリだけでなく、ローカル import の依存先をライブラリ単位で再帰的に含めた独立パッケージです。別の非公開リポジトリを clone する必要はありません。外部依存の mathlib とその依存は Lake が固定 revision から取得します。

| 深さ | ライブラリ | Lean ファイル数 |
|---:|---|---:|
| 1 | [ProCGroups](Lean4/ProCGroups/All.lean) | 724 |
| 1 | [ValuedFieldTheory](Lean4/ValuedFieldTheory/All.lean) | 591 |
| 1 | [GaloisCohomology](Lean4/GaloisCohomology/All.lean) | 309 |
| 1 | [SchemeTheory](Lean4/SchemeTheory/All.lean) | 975 |
| 2 | [ClassFieldTheory](Lean4/ClassFieldTheory/All.lean) | 1,246 |
| 2 | [AlgebraicCurves](Lean4/AlgebraicCurves/All.lean) | 2,452 |
| 2 | [EtaleFundamentalGroups](Lean4/EtaleFundamentalGroups/All.lean) | 1,608 |
| 2 | [EtaleCohomology](Lean4/EtaleCohomology/All.lean) | 125 |
| 3 | [JacobianVarieties](Lean4/JacobianVarieties/All.lean) | 485 |
| 3 | [AnabelianGeometry](Lean4/AnabelianGeometry/All.lean) | 44 |

パッケージ全体の入口は [`All`](Lean4/All.lean) です。各ライブラリの元のモジュール名を保持しているため、重複するソースを含む他の分割パッケージと同じ Lake 環境へ重ねて導入することは想定していません。

## ビルドと CI

Lean は [`lean-toolchain`](lean-toolchain) の **4.35.0-rc2**、mathlib は [`lakefile.toml`](lakefile.toml) の **065356127b1dc0016f66b7283ce0ce2c4055aa55** に固定しています。再現時は同梱の [`lake-manifest.json`](lake-manifest.json) を使います。

Git と [elan](https://github.com/leanprover/elan) を用意して実行します。

```sh
git clone https://github.com/n-yamaguchi-0729/AnabelianGeometry.git
cd AnabelianGeometry
lake exe cache get Mathlib
python3 .github/scripts/audit.py
lake --wfail build +ProCGroups.All +ValuedFieldTheory.All +GaloisCohomology.All +SchemeTheory.All
lake --wfail build +ClassFieldTheory.All +AlgebraicCurves.All +EtaleFundamentalGroups.All +EtaleCohomology.All
lake --wfail build +JacobianVarieties.All
lake build +AnabelianGeometry.All  # 下記の未証明定理1件の警告を表示
lake build +All  # 許可済みの未証明定理を含む
```

[`CI`](.github/workflows/lean.yml) は公開済みの [ProCGroups](https://github.com/n-yamaguchi-0729/ProCGroups)・[ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory)・[SawinTotallyRealTowers](https://github.com/n-yamaguchi-0729/SawinTotallyRealTowers) の版固定・依存深さ順の検証・成果物キャッシュの構成を参考にしています。今回の CI は次を行います。

- 全物理ソースと Lake glob、入口からの到達、import の欠落・循環・逆依存を静的検査。
- 深さ1、2、3のライブラリを順に通常ビルドし、最後に `+All` をビルド。
- `autoImplicit = false`、未使用引数、文書化、mathlib 標準 linter を Lake 設定で有効化。
- 段階間でプロジェクトのコンパイル成果物を再利用し、失敗時も診断ログを保存。

通常は `lake --wfail build` を使います。AnabelianGeometry の1件だけは既存の厳密な診断分類で未証明として表示し、それ以外の警告・エラーを失敗にします。新たな `sorry` / `admit` / 独自 `axiom` は静的検査でも拒否します。静的検査は証明項の独立検証ではありません。この CI では NanoDa や別途の全宣言 kernel replay を実行したとは主張しません。

**private の push / pull request ではビルドジョブを開始せず、Actions の手動実行は可能**です。public に切り替えた後は push / pull request で動作します。初回配布では private のまま作成し、公開設定の変更も CI の手動起動も行っていません。

初回の検証結果と検証範囲は [VALIDATION.md](VALIDATION.md) に記録しています。

## ソースの来歴

分割元、固定コミット、同梱ファイルの SHA-256 は [SOURCE_SNAPSHOT.json](SOURCE_SNAPSHOT.json) にあります。Lean 本文・既存の著作権表示は分割元から変更せず、配布用 `Lean4/All.lean`、Lake の対象範囲、README と CI を作成しました。ライブラリ内の既存計画には古い配置・当時の停止点が残る場合があります。

[第三者由来のコードと帰属](THIRD_PARTY.md) および [pi1 の25ファイル対応表](PI1_ATTRIBUTION.md) も参照してください。
