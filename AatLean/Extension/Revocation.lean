import AatLean.Invoke

/-!
# Т5. Отзыв корня — расширение по §9.8 AAT-02

AAT-02 «defines no revocation mechanism» (§9.8). Спецификация называет один
механизм, совместимый с проверкой цепочки: статус корневых токенов (например,
status list) — «revokes every chain that starts at a revoked root, and so every
token derived from it». Промежуточное звено так отозвать нельзя: это
ограничение спецификации, а не модели.

Снимок отзывов `R` — идентификаторы (`jti`) отозванных корней. Он не входит
во входы §8, поэтому живёт здесь, а не в сигнатуре `verify`. Допущение 4:
снимок свежее, чем Δ.
-/

namespace AAT

/-- `verify` и проверка статуса корня. -/
def verifyWithStatus (P : Params) (anchors : List Anchor) (revoked : List String)
    (chain : List Link) : Decision :=
  match chain with
  | [] => .deny
  | root :: _ => if revoked.contains root.jti then .deny else verify P anchors chain

/-- Вызов целиком с проверкой статуса корня. -/
def invokeWithStatus (P : Params) (E : Endpoint) (anchors : List Anchor) (revoked : List String)
    (chain : List Link) (call : Call) (pop : PoP) : Decision :=
  match verifyWithStatus P anchors revoked chain with
  | .allow => invoke P E anchors chain call pop
  | .deny => .deny

/-- **Т5.** Корень принятой цепочки не отозван, и цепочка проходит `verify`
    (поэтому на неё распространяются Т1, Т3–Т7). -/
theorem t5_revocation {P : Params} {anchors : List Anchor} {revoked : List String}
    {c : List Link} (h : verifyWithStatus P anchors revoked c = .allow) :
    ∃ root rest, c = root :: rest ∧ root.jti ∉ revoked ∧ verify P anchors c = .allow := by
  cases c with
  | nil => simp [verifyWithStatus] at h
  | cons r rest =>
    simp only [verifyWithStatus] at h
    split at h
    · simp at h
    · rename_i hn
      exact ⟨r, rest, rfl, by simpa [List.contains_iff_mem] using hn, h⟩

/-- **Т5′.** Отзыв корня отклоняет **каждую** цепочку, которая с него
    начинается, — любой длины и с любыми производными токенами. -/
theorem t5_revokes_descendants (P : Params) (anchors : List Anchor) (revoked : List String)
    (root : Link) (rest : List Link) (hr : root.jti ∈ revoked) :
    verifyWithStatus P anchors revoked (root :: rest) = .deny := by
  simp [verifyWithStatus, hr]

/-- Вызов с отозванным корнем отклоняется при любом PoP. -/
theorem t5_invoke (P : Params) (E : Endpoint) (anchors : List Anchor) (revoked : List String)
    (root : Link) (rest : List Link) (call : Call) (pop : PoP) (hr : root.jti ∈ revoked) :
    invokeWithStatus P E anchors revoked (root :: rest) call pop = .deny := by
  simp [invokeWithStatus, t5_revokes_descendants P anchors revoked root rest hr]

-- Ловушки
example : verifyWithStatus PT anchorsT [] good = .allow := by decide +kernel
example : verifyWithStatus PT anchorsT ["j0"] good = .deny := by decide +kernel
-- отзыв промежуточного звена спецификацией не предусмотрен: цепочка проходит
example : verifyWithStatus PT anchorsT ["j1"] good = .allow := by decide +kernel
example : invokeWithStatus PT ET anchorsT [] (mk chainT) callT popT = .allow := by decide +kernel
example : invokeWithStatus PT ET anchorsT ["j0"] (mk chainT) callT popT = .deny := by decide +kernel

end AAT
