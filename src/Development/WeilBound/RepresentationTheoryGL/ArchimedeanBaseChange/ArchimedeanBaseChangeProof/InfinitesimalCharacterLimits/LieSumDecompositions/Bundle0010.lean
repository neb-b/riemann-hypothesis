module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0008
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0007
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.IntegrableDescendSupP
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.CptRepMemTypePart
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0009

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.LeafHolds2
section
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open Leaf2Aux in
theorem leaf_holds2 : Leaf :=
  leaf_of (core_of (pairLin_of intBnd) pairRt (pairLie_of intBnd) growQHolds) growPHolds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmA
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

theorem factor {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (U : Submodule ℂ M)
    (T : M →ₗ[ℂ] N) (T' : M →ₗ[ℂ] N) (h : ∀ ψ ∈ U, T ψ = 0 → T' ψ = 0) :
    ∃ P : N →ₗ[ℂ] N, ∀ ψ ∈ U, P (T ψ) = T' ψ := by
  let f := T ∘ₗ U.subtype
  let g := T' ∘ₗ U.subtype
  have hle : LinearMap.ker f ≤ LinearMap.ker g := fun x hx => h x.1 x.2 hx
  let g₀ := (LinearMap.ker f).liftQ g hle
  let h₀ : LinearMap.range f →ₗ[ℂ] N := g₀ ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨P, hP⟩ := LinearMap.exists_extend h₀
  refine ⟨P, fun ψ hψ => ?_⟩
  have e1 : P (T ψ) = h₀ ⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ :=
    LinearMap.congr_fun hP (⟨f ⟨ψ, hψ⟩, LinearMap.mem_range_self f _⟩ : LinearMap.range f)
  rw [e1]
  change g₀ (f.quotKerEquivRange.symm ⟨f ⟨ψ, hψ⟩, _⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem eq_of_levi {F₁ F₂ : Sm E (r + s)}
    (h₁ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₁.1 (unip x * g) = F₁.1 g)
    (h₂ : ∀ (x : BlockIx (r + s) r → Ad E) g, F₂.1 (unip x * g) = F₂.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F₁.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        F₂.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g))) : F₁ = F₂ := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨u, m, k, g, rfl⟩ := ParabolicProjection.exists_decomp x
  rw [mul_assoc, h₁, h₂]
  exact h k g m

theorem eq_zero_of_levi {F : Sm E (r + s)} (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (h : ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
      F.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) = 0) : F = 0 :=
  eq_of_levi hF (fun _ _ => rfl) h

theorem isStable_map {a : ℕ} {L : Submodule ℂ (Sm E a)} (hL : _root_.GlobalTheory.CuspRep.IsStable L) {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) : _root_.GlobalTheory.CuspRep.IsStable (L.map z) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨act o φ, hL o φ hφ, by
    change z (act o φ) = act o (z φ)
    rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]⟩

theorem finGen_map {a : ℕ} {L : Submodule ℂ (Sm E a)} {z : Module.End ℂ (Sm E a)}
    (hz : ∀ o : Op E a, Commute z (act o)) (S₁ : Finset (Sm E a)) (hS₁ : (↑S₁ : Set (Sm E a)) ⊆ L)
    (hgen : ∀ W : Submodule ℂ (Sm E a), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E a)) ⊆ W → L ≤ W) : FinGen (L.map z) := by
  classical
  refine ⟨S₁.image z, fun x hx => ?_, fun W hW hSW => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    exact Submodule.mem_map_of_mem (hS₁ hy)
  · have hst : _root_.GlobalTheory.CuspRep.IsStable (W.comap z) := fun o φ hφ => by
      change z (act o φ) ∈ W
      rw [← Module.End.mul_apply, (hz o).eq, Module.End.mul_apply]
      exact hW o _ hφ
    have hle := hgen (W.comap z) hst fun y hy => hSW (Finset.mem_coe.2 (Finset.mem_image_of_mem z hy))
    rintro _ ⟨φ, hφ, rfl⟩
    exact hle hφ

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgD
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

def HExp (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Prop :=
  ∀ ψ ∈ U, ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)), ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
    (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) k g)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) k g) ∧
    ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m * BlockDerivatives.yp k g) = ∑ i, (b i).1 m.1 * (q i).1 m.2

theorem lsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.lsF r s F k g, ∃ m₂, ℓ = sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₂, h⟩
  exact ⟨m₂, Subtype.ext (funext fun m₁ => by rw [h, left_slice_apply, rt_apply])⟩

theorem rsF_yp (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) :
    ∀ ℓ ∈ BlockDerivatives.rsF r s F k g, ∃ m₁, ℓ = sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k g) F) := by
  rintro ℓ ⟨m₁, h⟩
  exact ⟨m₁, Subtype.ext (funext fun m₂ => by rw [h, right_slice_apply, rt_apply])⟩

theorem rt_one {a : ℕ} (F : Sm E a) : rt E a (BlockDerivatives.yp 1 1) F = F := by
  rw [yp_one, map_one, Module.End.one_apply]

theorem lsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.lsF r s F 1 1, ∃ m₂, ℓ = sl0 m₂ F := by
  intro ℓ hℓ
  obtain ⟨m₂, h⟩ := lsF_yp F 1 1 ℓ hℓ
  exact ⟨m₂, by rw [h, rt_one]⟩

theorem rsF_one (F : Sm E (r + s)) : ∀ ℓ ∈ BlockDerivatives.rsF r s F 1 1, ∃ m₁, ℓ = sl1 m₁ F := by
  intro ℓ hℓ
  obtain ⟨m₁, h⟩ := rsF_yp F 1 1 ℓ hℓ
  exact ⟨m₁, by rw [h, rt_one]⟩

theorem exp_one {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hexp : HExp U T)
    {ψ : Sm E (r + s)} (hψ : ψ ∈ U) :
    ∃ (n : ℕ) (b : Fin n → Sm E r) (q : Fin n → Sm E s),
      (∀ i, b i ∈ Submodule.span ℂ (BlockDerivatives.lsF r s (T ψ) 1 1)) ∧ (∀ i, q i ∈ BlockDerivatives.rsF r s (T ψ) 1 1) ∧
      ∀ m : GA E r × GA E s, (T ψ).1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2 := by
  obtain ⟨n, b, q, hb, hq, he⟩ := hexp ψ hψ 1 1
  refine ⟨n, b, q, hb, hq, fun m => ?_⟩
  rw [← he m, yp_one, mul_one]

theorem rt_yp_eq {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    rt E a (BlockDerivatives.yp k g) φ = act (.cpt k) (act (.fin g) φ) := by
  rw [act_cpt_eq, act_fin_eq, rt_yp_rt, mul_one, one_mul]

theorem rt_yp_mem {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) (k : Kinf E a) (g : GL (Fin a) (Af E))
    {φ : Sm E a} (hφ : φ ∈ U) : rt E a (BlockDerivatives.yp k g) φ ∈ U := by
  rw [rt_yp_eq]
  exact hU _ _ (hU _ _ hφ)

theorem T_rt_yp {a : ℕ} {U : Submodule ℂ (Sm E a)} (hU : _root_.GlobalTheory.CuspRep.IsStable U) {T : Sm E a →ₗ[ℂ] Sm E a}
    (hT : ∀ o, ∀ φ ∈ U, T (act o φ) = act o (T φ)) (k : Kinf E a) (g : GL (Fin a) (Af E)) {φ : Sm E a}
    (hφ : φ ∈ U) : T (rt E a (BlockDerivatives.yp k g) φ) = rt E a (BlockDerivatives.yp k g) (T φ) := by
  rw [rt_yp_eq, rt_yp_eq, hT _ _ (hU _ _ hφ), hT _ _ hφ]

def Mleft (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E r)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₂ : GA E s),
    sl0 m₂ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₂ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₂) (hb.2 k g m₂)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₂ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₂ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₂)⟩

def Mright (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) (W : Submodule ℂ (Sm E s)) :
    Submodule ℂ (Sm E (r + s)) where
  carrier := {ψ | ψ ∈ U ∧ ∀ (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) (m₁ : GA E r),
    sl1 m₁ (T (rt E (r + s) (BlockDerivatives.yp k g) ψ)) ∈ W}
  add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, fun k g m₁ => by
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]; exact W.add_mem (ha.2 k g m₁) (hb.2 k g m₁)⟩
  zero_mem' := ⟨U.zero_mem, fun k g m₁ => by rw [map_zero, map_zero, map_zero]; exact W.zero_mem⟩
  smul_mem' := fun c a ha => ⟨U.smul_mem c ha.1, fun k g m₁ => by
    rw [map_smul, map_smul, map_smul]; exact W.smul_mem c (ha.2 k g m₁)⟩

theorem Mleft_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E r))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mleft U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₂
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₂
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₂ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₂, sl0 m₂ (T ψ') ∈ W := fun m₂ => hψ k g m₂
    obtain ⟨n, b, q, hb, -, he⟩ := exp_one hexp hψ'U
    have hsub : BlockDerivatives.lsF r s (T ψ') 1 1 ⊆ W := fun ℓ hℓ => by
      obtain ⟨m, rfl⟩ := lsF_one _ ℓ hℓ
      exact hP m
    have hbW : ∀ i, b i ∈ W := fun i => (Submodule.span_le.2 hsub) (hb i)
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_left W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hbW he _ (par_low X') m₂) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl0 m₂ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl0 m₂ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₂)
    exact hle hmem

theorem Mright_stable {U : Submodule ℂ (Sm E (r + s))} (hU : IsAutSt U) {c : ℂ}
    {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} (hT : IsSliceMap U c T) (hexp : HExp U T) (W : Submodule ℂ (Sm E s))
    (hW : _root_.GlobalTheory.CuspRep.IsStable W) : _root_.GlobalTheory.CuspRep.IsStable (Mright U T W) := by
  rintro o ψ ⟨hψU, hψ⟩
  cases o with
  | fin h =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_fin_eq, rt_yp_rt, mul_one]
    exact hψ k (g * h) m₁
  | cpt κ =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    rw [act_cpt_eq, rt_yp_rt, mul_one]
    exact hψ (k * κ) g m₁
  | lie X =>
    refine ⟨hU.1 _ _ hψU, fun k g m₁ => ?_⟩
    obtain ⟨X', hX'⟩ := rt_lie_yp k g X
    have hψ'U : rt E (r + s) (BlockDerivatives.yp k g) ψ ∈ U := rt_yp_mem hU.1 k g hψU
    have e1 : rt E (r + s) (BlockDerivatives.yp k g) (act (.lie X) ψ) = lie E (r + s) X' (rt E (r + s) (BlockDerivatives.yp k g) ψ) :=
      LinearMap.congr_fun hX' ψ
    rw [e1]
    have e2 := hT.equiv (.lie X') _ hψ'U
    change T (lie E (r + s) X' _) = lie E (r + s) X' _ at e2
    rw [e2]
    set ψ' := rt E (r + s) (BlockDerivatives.yp k g) ψ with hψ'
    have hP : ∀ m₁, sl1 m₁ (T ψ') ∈ W := fun m₁ => hψ k g m₁
    obtain ⟨n, b, q, -, hq, he⟩ := exp_one hexp hψ'U
    have hqW : ∀ i, q i ∈ W := fun i => by
      obtain ⟨m, hm⟩ := rsF_one _ _ (hq i)
      rw [hm]
      exact hP m
    rw [lie_split, map_add (f := _)]
    refine W.add_mem (key_right W hW (T ψ') (hT.unipInv ψ' hψ'U) hP b q hqW he _ (par_low X') m₁) ?_
    have e3 := hT.equiv (.lie (toL (skw X'))) _ hψ'U
    change T (lie E (r + s) (toL (skw X')) ψ') = lie E (r + s) (toL (skw X')) (T ψ') at e3
    rw [← e3]
    have : FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan ψ') := (hU.2 ψ' hψ'U).kfin
    have hmem := lie_mem_orbSpan ψ' (skw X') (skw_skew X')
    have hle : GlobalTheory.CuspRep.LocEx.orbSpan ψ' ≤ W.comap (sl1 m₁ ∘ₗ T) := Submodule.span_le.2 (by
      rintro _ ⟨κ, rfl⟩
      change sl1 m₁ (T (act (.cpt κ) ψ')) ∈ W
      rw [act_cpt_eq, hψ', rt_yp_rt, one_mul]
      exact hψ (κ * k) g m₁)
    exact hle hmem

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksLag
section
noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockLagrange

section Abs

variable {M ι Λ : Type} [AddCommGroup M] [Module ℂ M] [DecidableEq ι]

theorem list_prod_apply (l : List (Module.End ℂ M)) (k : Module.End ℂ M → ℂ) (φ : M) (h : ∀ f ∈ l, f φ = k f • φ) :
    l.prod φ = (l.map k).prod • φ := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih (fun g hg => h g (List.mem_cons_of_mem _ hg)), map_smul,
      h f List.mem_cons_self, smul_smul, List.map_cons, List.prod_cons, mul_comm]

theorem list_prod_smul (l : List (Module.End ℂ M)) (φ : M) (h : ∀ f ∈ l, ∃ c : ℂ, f φ = c • φ) :
    ∃ c : ℂ, l.prod φ = c • φ := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons f l ih =>
    obtain ⟨c, hc⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    obtain ⟨d, hd⟩ := h f List.mem_cons_self
    exact ⟨c * d, by rw [List.prod_cons, Module.End.mul_apply, hc, map_smul, hd, smul_smul]⟩

variable (A : Λ → Module.End ℂ M) (χ : ι → Λ → ℂ) (lam : ι → ι → Λ)

def fac (i j : ι) : Module.End ℂ M := (χ i (lam i j) - χ j (lam i j))⁻¹ • (A (lam i j) - χ j (lam i j) • 1)

def proj (SS : Finset ι) (i : ι) : Module.End ℂ M := (((SS.erase i).toList).map (fac A χ lam i)).prod

variable {A χ lam}

omit [DecidableEq ι] in
theorem fac_apply {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ) (i j k : ι) {φ : M}
    (hφ : φ ∈ P k) :
    fac A χ lam i j φ = ((χ i (lam i j) - χ j (lam i j))⁻¹ * (χ k (lam i j) - χ j (lam i j))) • φ := by
  simp only [fac, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hP k φ hφ]
  rw [smul_sub, smul_smul, smul_smul, mul_sub, sub_smul]

theorem proj_self {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (hlam : ∀ i j, i ≠ j → χ i (lam i j) ≠ χ j (lam i j)) (SS : Finset ι) (i : ι) {φ : M} (hφ : φ ∈ P i) :
    proj A χ lam SS i φ = φ := by
  unfold proj
  rw [list_prod_apply _ (fun _ => 1) φ]
  · simp
  · intro f hf
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
    rw [one_smul, fac_apply hP i j i hφ]
    have hij : i ≠ j := fun h => by subst h; exact Finset.notMem_erase i SS (Finset.mem_toList.1 hj)
    rw [inv_mul_cancel₀ (sub_ne_zero.2 (hlam i j hij)), one_smul]

theorem proj_other {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (SS : Finset ι) (i k : ι) (hk : k ∈ SS) (hki : k ≠ i) {φ : M} (hφ : φ ∈ P k) :
    proj A χ lam SS i φ = 0 := by
  unfold proj
  have hmem : fac A χ lam i k ∈ ((SS.erase i).toList).map (fac A χ lam i) :=
    List.mem_map.2 ⟨k, Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hki, hk⟩), rfl⟩
  obtain ⟨l₁, l₂, he⟩ := List.append_of_mem hmem
  have hl₂ : ∀ f ∈ l₂, ∃ c : ℂ, f φ = c • φ := by
    intro f hf
    have hf' : f ∈ ((SS.erase i).toList).map (fac A χ lam i) := by
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf'
    exact ⟨_, fac_apply hP i j k hφ⟩
  obtain ⟨c, hc⟩ := list_prod_smul l₂ φ hl₂
  rw [he, List.prod_append, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul,
    fac_apply hP i k k hφ, sub_self, mul_zero, zero_smul, smul_zero, map_zero]

theorem proj_decomp {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (hlam : ∀ i j, i ≠ j → χ i (lam i j) ≠ χ j (lam i j)) (SS : Finset ι) {φ : M} (hφ : φ ∈ ⨆ i ∈ SS, P i) :
    (∀ i, proj A χ lam SS i φ ∈ P i) ∧ ∑ i ∈ SS, proj A χ lam SS i φ = φ := by
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum P φ).1 hφ
  have key : ∀ i, proj A χ lam SS i φ = if i ∈ SS then (μ i : M) else 0 := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hμ, map_sum]
    rw [Finset.sum_congr rfl (g := fun k => if k = i then (μ k : M) else 0) (fun k hk => by
      by_cases h : k = i
      · subst h; rw [if_pos rfl, proj_self hP hlam SS k (μ k).2]
      · rw [if_neg h, proj_other hP SS i k hk h (μ k).2])]
    rw [Finset.sum_ite_eq']
  refine ⟨fun i => ?_, ?_⟩
  · rw [key]
    split_ifs
    · exact (μ i).2
    · exact (P i).zero_mem
  · rw [Finset.sum_congr rfl (fun i hi => by rw [key, if_pos hi]), hμ]

theorem proj_commute (SS : Finset ι) (i : ι) (B : Module.End ℂ M) (hB : ∀ l, Commute (A l) B) :
    Commute (proj A χ lam SS i) B := by
  unfold proj
  refine Commute.list_prod_left _ _ fun f hf => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf
  exact ((hB _).sub_left ((Commute.one_left B).smul_left _)).smul_left _

end Abs

section Sep

theorem exists_ne_prod {m m' : Multiset ℂ} (sh : ℂ) (h : m ≠ m') :
    ∃ w : ℂ, (m.map fun z => w + sh + z).prod ≠ (m'.map fun z => w + sh + z).prod := by
  by_contra hc
  push Not at hc
  have ev : ∀ (n : Multiset ℂ) (w : ℂ), (n.map fun z => w + sh + z).prod =
      ((n.map fun z => -(sh + z)).map fun a => X - C a).prod.eval w := by
    intro n w
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp
    ring
  have hp : ((m.map fun z => -(sh + z)).map fun a => X - C a).prod =
      ((m'.map fun z => -(sh + z)).map fun a => X - C a).prod :=
    Polynomial.funext fun w => by rw [← ev, ← ev, hc w]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact h (Multiset.map_injective (fun x y hxy => by simpa using hxy) hr)

end Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem proj_exists {a : ℕ} (L : Submodule ℂ (Sm E a)) (SS : Finset ((E →+* ℂ) → Multiset ℂ)) (sh : ℂ)
    (hL : L ≤ ⨆ σ ∈ SS, BlockCapelli.Eig L σ sh) :
    ∃ z : ((E →+* ℂ) → Multiset ℂ) → Module.End ℂ (Sm E a), (∀ σ (o : Op E a), Commute (z σ) (act o)) ∧
      (∀ σ, ∀ φ ∈ L, z σ φ ∈ BlockCapelli.Eig L σ sh) ∧ ∀ φ ∈ L, ∑ σ ∈ SS, z σ φ = φ := by
  classical
  let A : (E →+* ℂ) × ℂ → Module.End ℂ (Sm E a) := fun l => cap l.1 l.2
  let χ : ((E →+* ℂ) → Multiset ℂ) → (E →+* ℂ) × ℂ → ℂ := fun σ l => ((σ l.1).map fun z => l.2 + sh + z).prod
  have hsep : ∀ σ σ' : (E →+* ℂ) → Multiset ℂ, σ ≠ σ' → ∃ l, χ σ l ≠ χ σ' l := by
    intro σ σ' h
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
    obtain ⟨w, hw⟩ := exists_ne_prod sh hτ
    exact ⟨(τ, w), hw⟩
  let lam : ((E →+* ℂ) → Multiset ℂ) → ((E →+* ℂ) → Multiset ℂ) → (E →+* ℂ) × ℂ := fun σ σ' =>
    if h : σ ≠ σ' then Classical.choose (hsep σ σ' h) else (Classical.arbitrary _, 0)
  have hlam : ∀ σ σ', σ ≠ σ' → χ σ (lam σ σ') ≠ χ σ' (lam σ σ') := by
    intro σ σ' h
    simp only [lam, dif_pos h]
    exact Classical.choose_spec (hsep σ σ' h)
  have hP : ∀ k, ∀ φ ∈ BlockCapelli.Eig L k sh, ∀ l, A l φ = χ k l • φ := fun k φ hφ l => hφ.2 l.1 l.2
  refine ⟨proj A χ lam SS, fun σ o => proj_commute SS σ _ fun l => GlobalTheory.SpehInfChar.cap_commute_act l.1 l.2 o,
    fun σ φ hφ => (proj_decomp hP hlam SS (hL hφ)).1 σ, fun φ hφ => (proj_decomp hP hlam SS (hL hφ)).2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockLagrange

end
end

