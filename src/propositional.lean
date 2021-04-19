namespace propositional

inductive L₁ (L₀ : Type)
| not : L₁ → L₁
| and : L₁ → L₁ → L₁
| var : L₀ → L₁

end propositional