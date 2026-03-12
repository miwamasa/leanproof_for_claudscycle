Lean 4形式化 (ClaudeCycles.lean) は以下を含みます:

定義: 頂点 Fin m × Fin m × Fin m、方向型 Dir、ファイバーインデックス fiberIndex、バンプ関数 bump、3つのサイクルの方向関数 dir0/dir1/dir2
主要定理の文: cycle0_hamiltonian, cycle1_hamiltonian, cycle2_hamiltonian, 統合定理 claude_decomposition
証明の骨格: Knuthの証明に沿った補題群（cycle0_i_change_condition, checkpoints0_injective, i0_block_complete, block_exit_bumps_i 等）
一般化可能性の定義: Knuthの「Claude-like分解」の概念を ClaudeLike 構造体として形式化

核心的な数学的ステップ（gcd(2,m)=1 による全射性、各i-ブロック内の完全性）は sorry のまま残していますが、補題 Lemmas.lean に証明戦略の詳細な記述を付けています。
テスト (13テスト全通過):

ファイバー進行、方向の置換性、i変化条件、チェックポイント被覆、ブロック連続性、ハミルトン性（m=3〜17）、弧の分割、Knuth論文の具体例との照合、非一般化可能サイクルの検証

Lean 4はこの環境にインストールできなかったため、ローカルで lake build して型検査することをお勧めします。Mathlibの ZMod と Fin の算術補題を使えば、sorry の多くは段階的に埋められるはずです。