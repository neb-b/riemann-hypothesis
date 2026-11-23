module

public import Formalism.CharacterColumnKernels.StatGlobalModule
public import Formalism.CharacterColumnKernels.StatementMF

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

section Coh
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

def coZ1s (ρ : Representation O G M) : Submodule O (G → M) where
  carrier := {c | ∀ g h, c (g * h) = c g + ρ g (c h)}
  add_mem' {a b} ha hb g h := by
    simp only [Pi.add_apply, ha g h, hb g h, map_add (f := _)]; abel
  zero_mem' g h := by simp
  smul_mem' r c hc g h := by
    simp only [Pi.smul_apply, hc g h, smul_add, map_smul]

def resRep (ρ : Representation O G M) (D : Subgroup G) : Representation O D M :=
  ρ.comp D.subtype

def restrictCocycles1 (ρ : Representation O G M) (D : Subgroup G) : coZ1s ρ →ₗ[O] coZ1s (resRep ρ D) where
  toFun c := ⟨fun g => (c : G → M) g, fun g h => c.2 g h⟩
  map_add' a b := rfl
  map_smul' r a := rfl

abbrev H1z (ρ : Representation O G M) : Type _ := coZ1s ρ ⧸ (coB1 ρ).comap (coZ1s ρ).subtype

def resH1 (ρ : Representation O G M) (D : Subgroup G) : H1z ρ →ₗ[O] H1z (resRep ρ D) :=
  Submodule.mapQ _ _ (restrictCocycles1 ρ D) (by
    rintro x ⟨v, hv⟩
    exact ⟨v, funext fun g => congrFun hv g⟩)

end Coh

def annih {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw] [AddCommGroup Cs]
    [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P) (U : Submodule O Cs) :
    Submodule O Cw :=
  ⨅ x ∈ U, LinearMap.ker (pr.flip x)

def StatLenChain : Prop :=
  ∀ (O H Zc C : Type*) [CommRing O] [AddCommGroup H] [Module O H] [AddCommGroup Zc] [Module O Zc]
    [AddCommGroup C] [Module O C] (Ψ : H →ₗ[O] Zc) (cl : Zc →ₗ[O] C) (S : Submodule O C),
    LinearMap.range (cl ∘ₗ Ψ) ≤ S →
    Module.length O H ≤ Module.length O (LinearMap.ker Ψ) +
      Module.length O ↥(LinearMap.range Ψ ⊓ LinearMap.ker cl) + Module.length O S

def StatSelRelax : Prop :=
  ∀ (O C ι : Type*) [CommRing O] [AddCommGroup C] [Module O C] (what₂ : Finset ι)
    (Cw : ι → Type*) [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)] (res : ∀ w, C →ₗ[O] Cw w)
    (F F' : ∀ w, Submodule O (Cw w)) (Q : Submodule O C), (∀ w, F w ≤ F' w) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w)) ≤
      Module.length O ↥(Q ⊓ ⨅ w ∈ what₂, (F w).comap (res w)) +
        ∑ w ∈ what₂, Module.length O (F' w ⧸ (F w).comap (F' w).subtype)

def StatAnnColength : Prop :=
  ∀ (O Cw Cs : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup Cw]
    [Module O Cw] [AddCommGroup Cs] [Module O Cs] (pr : Cw →ₗ[O] Cs →ₗ[O] KO O),
    ∀ (Fs Im : Submodule O Cs), Im ≤ Fs →
    Module.length O (annih pr Im ⧸ (annih pr Fs).comap (annih pr Im).subtype) ≤
      Module.length O (Fs ⧸ Im.comap Fs.subtype)

def StatTorsLen : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (d : Type) [Fintype d]
    (δ : O),
    Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) (δ * δ))) =
      (Fintype.card d : ℕ∞) * (2 * IsDiscreteValuationRing.addVal O δ)

end Formalism.NG
