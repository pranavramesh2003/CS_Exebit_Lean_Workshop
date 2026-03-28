import Lean

/-

Any family of types can be marked as a type class.
 We can then declare particular elements of a type class to be instances.
 These provide hints to the elaborator: any time the elaborator is looking for an element of a type class,
  it can consult a table of declared instances to find a suitable element.
-/

class inhabited (α : Type _) where
(default : α)

instance Prop_inhabited : inhabited Prop :=
inhabited.mk True

instance bool_inhabited : inhabited Bool :=
inhabited.mk true

instance nat_inhabited : inhabited Nat :=
inhabited.mk 0

instance unit_inhabited : inhabited Unit :=
inhabited.mk ()

def default (α : Type u) [s : inhabited α] : α :=
@inhabited.default α s

instance prod_inhabited
    {α β : Type u} [inhabited α] [inhabited β] :
  inhabited (Prod α β) :=
⟨(default α, default β)⟩

#eval default (Nat × Bool)


instance inhabited_fun (α : Type u) {β : Type v} [inhabited β] :
  inhabited (α → β) :=
⟨(λ a : α => default β)⟩

#check default (Nat → Nat ×  Bool)
#reduce default (Nat → Nat ×  Bool)
