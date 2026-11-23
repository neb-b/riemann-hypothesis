module

public import Mathlib
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0553
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JacquetFunctionalClass
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_irr {h : ℕ} (x : Fin h → IrrGL (k := k)) : (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ _ (x a).2.rep.irr
      (CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem jm_ne_top {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) : jm x hd π ≠ ⊤ :=
  jhMult_ne_top (piTensor_irr x)
    (_root_.GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) V π hπ hl)

theorem jm_congr {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (hπ : IsSmooth π) (hτ : IsSmooth τ) (φ : π.Equiv τ) : jm x hd π = jm x hd τ :=
  le_antisymm (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd π τ hτ (.of_injective φ.toIntertwiningMap φ.injective))
    (GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient x hd τ π hπ (.of_surjective φ.toIntertwiningMap φ.surjective))

theorem jm_eq_sum {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsSmooth π) (hl : HasFiniteLength π) :
    jm x hd π = ∑ c ∈ (finite_constituents hl).toFinset, jhMult c.rep.ρ π * jm x hd c.rep.ρ := by
  set F := (finite_constituents hl).toFinset with hF
  have hσ := piTensor_irr x
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation π,
      jm x hd S.toRepresentation = ∑ c ∈ F, jhMult c.rep.ρ S.toRepresentation * jm x hd c.rep.ρ := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hne
    · have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation
          (unipRad k (stdBlocks (fun a => (x a).1) hd))) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      rw [jm, jhMult_of_subsingleton hσ]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [jhMult_of_subsingleton c.rep.irr, zero_mul]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hqπ : IsSubquotient (subQuot S T) π := hq.trans (.of_injective j Subtype.val_injective)
    have hsm : IsSmooth (subQuot S T) := hqπ.isSmooth hπ
    have hirr : (subQuot S T).IsIrreducible := isIrreducible_subQuot hT
    let τ : IrrRep (GL (Fin N) k) := ⟨_, subQuot S T, hsm, hirr⟩
    have hsplit : jm x hd S.toRepresentation = jm x hd T.toRepresentation + jm x hd (subQuot S T) :=
      GlobalTheory.CompanionTheory.WordIrr.jhMult_jac_of_le _ hσ hπ hT.le
    have hmult : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ T.toRepresentation + jhMult c.rep.ρ (subQuot S T) :=
      fun c => jhMult_of_le c.rep.irr hT.le
    have hzero : ∀ c : IrrCl (GL (Fin N) k), c ≠ τ.cl → jhMult c.rep.ρ (subQuot S T) = 0 := by
      intro c hc
      by_contra h0
      obtain ⟨ψ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr hirr
      exact hc (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨ψ.symm⟩))
    obtain ⟨ψ⟩ := τ.nonempty_equiv_rep
    have hone : jhMult τ.cl.rep.ρ (subQuot S T) = 1 := by
      rw [jhMult_congr_left ψ]
      exact jhMult_self hirr
    have hmem : τ.cl ∈ F := by
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      have := GlobalTheory.CompanionTheory.JmMono.jhMult_le_of_isSubquotient τ.cl.rep.ρ hqπ
      rw [hone, h0] at this
      exact absurd this (by simp)
    have hQ : jm x hd (subQuot S T) = ∑ c ∈ F, jhMult c.rep.ρ (subQuot S T) * jm x hd c.rep.ρ := by
      rw [Finset.sum_eq_single_of_mem τ.cl hmem (fun c _ hc => by rw [hzero c hc, zero_mul]), hone, one_mul]
      exact (jm_congr x hd τ.cl.rep.smooth hsm ψ).symm
    rw [hsplit, ih T hT.lt, hQ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hmult c, add_mul]
  have hT1 : IsSmooth (⊤ : Subrepresentation π).toRepresentation :=
    (IsSubquotient.of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective).isSmooth hπ
  rw [← jm_congr x hd hT1 hπ (topEquiv π), key ⊤]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [jhMult_congr_right _ (topEquiv π)]

end CompanionTheory.Groth.JClsPf

namespace CompanionTheory.Groth

open CompanionTheory.Groth.JClsPf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem jacquet_functional_class (W : List (IrrGL (k := k))) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hl : HasFiniteLength π) :
    J W (cl0 π) = (cls π hl).sum fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k)))).toNat : ℤ) := by
  unfold J cl0
  rw [dif_pos hl, clsGL, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]


variable (k) in
theorem jCls : JCls k := by
  intro W N V _ _ π hπ hl
  by_cases hd : ∑ a, (W.get a).1 = N
  · have hjπ : jmL W π = jm W.get hd π := dif_pos hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k))) = jm W.get hd c.rep.ρ :=
      fun c => dif_pos hd
    refine ⟨by rw [hjπ]; exact jm_ne_top W.get hd π hπ hl, ?_⟩
    set F := (finite_constituents hl).toFinset with hF
    have ha : ∀ c : IrrCl (GL (Fin N) k), jhMult c.rep.ρ π ≠ ⊤ := fun c => jhMult_ne_top c.rep.irr hl
    have hb : ∀ c : IrrCl (GL (Fin N) k), jm W.get hd c.rep.ρ ≠ ⊤ :=
      fun c => jm_ne_top W.get hd c.rep.ρ c.rep.smooth c.rep.hasFiniteLength
    have hsum : jm W.get hd π =
        ((∑ c ∈ F, (jhMult c.rep.ρ π).toNat * (jm W.get hd c.rep.ρ).toNat : ℕ) : ℕ∞) := by
      rw [jm_eq_sum W.get hd π hπ hl, Nat.cast_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Nat.cast_mul, ENat.natCast_toNat (ha c), ENat.natCast_toNat (hb c)]
    have hsub : (cls π hl).support ⊆ F := by
      intro c hc
      rw [Finsupp.mem_support_iff, cls_apply] at hc
      rw [hF, Set.Finite.mem_toFinset]
      intro h0
      exact hc (by rw [h0]; rfl)
    rw [jacquet_functional_class W π hl, hjπ, hsum, ENat.toNat_natCast, Nat.cast_sum,
      Finsupp.sum_of_support_subset (cls π hl) hsub
        (fun c m => m * ((jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k)))).toNat : ℤ)) (fun c _ => zero_mul _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hjc c, cls_apply, Nat.cast_mul]
  · have hjπ : jmL W π = 0 := dif_neg hd
    have hjc : ∀ c : IrrCl (GL (Fin N) k), jmL W (IrrGL.rep (⟨N, c⟩ : IrrGL (k := k))) = 0 := fun c => dif_neg hd
    refine ⟨by rw [hjπ]; exact ENat.zero_ne_top, ?_⟩
    rw [jacquet_functional_class W π hl, hjπ]
    simp [hjc, Finsupp.sum]

end CompanionTheory.Groth

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JhMultSegCl
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SegJ


open Classical in
theorem jhMult_seg_cl (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (y : Fin Δ.len → IrrCl (GL (Fin Δ.d) k)) (hd : ∑ _ : Fin Δ.len, Δ.d = Δ.len * Δ.d) :
    jhMult (piTensor fun a => (y a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) =
      if (∀ a, (⟨Δ.d, y a⟩ : IrrGL (k := k)) = Δ.term a) then 1 else 0 := by
  obtain ⟨Φ⟩ := ((hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep).2).1
    (Z Δ).cl_rep
  let Ψ : (piTensor (segTerm Δ.start.rep.ρ Δ.len)).Equiv (piTensor fun a => (Δ.term a).rep) :=
    piTensorEquiv fun _ => Δ.first.twEquiv _ (isSmoothChar_absPow _)
  have hT : (piTensor fun a => (Δ.term a).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA Δ.term
  rw [jhMult_congr_right _ (Φ.trans Ψ)]
  split_ifs with h
  · have hy : ∀ a, y a = (Δ.term a).2 := fun a => eq_of_heq (Sigma.mk.inj_iff.1 (h a)).2
    obtain rfl : y = fun a => (Δ.term a).2 := funext hy
    exact jhMult_self hT
  · by_contra hne
    have hy : (piTensor fun a => (y a).rep.ρ).IsIrreducible :=
      GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (fun a => (⟨Δ.d, y a⟩ : IrrGL (k := k)))
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hy hT (jhMult_ne_zero_iff.1 hne)
    have hcl := _root_.GlobalTheory.TensorFactorUnique.cl_eq_of_piTensor_equiv (Fin Δ.len) (fun _ => GL (Fin Δ.d) k) (fun a => (Δ.term a).2.rep)
      (fun a => (y a).rep) ⟨φ⟩
    refine h fun a => ?_
    have h1 : (Δ.term a).2 = y a := (IrrCl.cl_rep _).symm.trans ((hcl a).trans (IrrCl.cl_rep _))
    rw [← h1]
    rfl


open Classical in
theorem jm_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    {m : ℕ} (y : Fin m → IrrGL (k := k)) (hy : ∀ a, (y a).1 = Δ.d) (hd : ∑ a, (y a).1 = Δ.len * Δ.d) :
    jm y hd (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) =
      if ∃ h : m = Δ.len, ∀ a, y a = Δ.term (Fin.cast h a) then 1 else 0 := by
  have hm : m = Δ.len := by
    have h1 : ∑ a, (y a).1 = m * Δ.d := by simp [hy]
    exact Nat.eq_of_mul_eq_mul_right Δ.d_pos (h1.symm.trans hd)
  subst hm
  obtain ⟨y', rfl⟩ : ∃ y' : Fin Δ.len → IrrCl (GL (Fin Δ.d) k), y = fun a => ⟨Δ.d, y' a⟩ :=
    ⟨fun a => cast (congrArg (fun n => IrrCl (GL (Fin n) k)) (hy a)) (y a).2,
      funext fun a => Sigma.ext (hy a) (cast_heq _ _).symm⟩
  show jhMult (piTensor fun a => (y' a).rep.ρ) (jac (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (Z Δ).rep.ρ) = _
  rw [jhMult_seg_cl hA hZ Δ y' hd]
  congr 1
  exact propext ⟨fun h => ⟨rfl, fun a => by simpa using h a⟩, fun ⟨_, h⟩ a => by simpa using h a⟩


open Classical in
theorem jmL_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k)
    (W : List (IrrGL (k := k))) (hW : ∀ w ∈ W, w.1 = Δ.d) (hl : W.length = Δ.len) :
    jmL W (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k))) = if W = List.ofFn Δ.term then 1 else 0 := by
  have hy : ∀ a, (W.get a).1 = Δ.d := fun a => hW _ (List.get_mem _ _)
  have hd : ∑ a, (W.get a).1 = Δ.len * Δ.d := by
    rw [Finset.sum_congr rfl fun a _ => hy a]
    simp [hl]
  unfold jmL
  rw [dite_eq_left hd, jm_seg hA hZ Δ W.get hy hd]
  congr 1
  refine propext ⟨fun ⟨h, h2⟩ => ?_, ?_⟩
  · refine List.ext_get (by simp [h]) fun n h1 h3 => ?_
    simpa using h2 ⟨n, h1⟩
  · rintro rfl
    exact ⟨List.length_ofFn, fun a => by simp; rfl⟩

theorem vWord_ne (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (S : Finset (Fin Δ.len))
    (hS : S ∈ vSets Δ) (hne : S ≠ ∅) : vWord Δ S ≠ List.ofFn Δ.term := by
  intro H
  rw [vWord, List.ofFn_eq_map] at H
  have H2 := (List.map_injective_iff.2 (_root_.GlobalTheory.CompanionTheory.SegTerm.term_injective hA Δ)) H
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have hL1 : ((List.finRange Δ.len).filter fun a => a ∈ S) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.2 ⟨List.mem_finRange s, by simpa using hs⟩)
  obtain ⟨x, t, hxt⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.2 hL1)
  have hx : x ∈ S := by
    have : x ∈ ((List.finRange Δ.len).filter fun a => a ∈ S).reverse := hxt ▸ List.mem_cons_self ..
    simpa using this
  rw [hxt] at H2
  have h0 := congrArg (fun L => L[0]?) H2
  simp at h0
  have h3 := (Finset.mem_filter.1 hS).2 x hx
  rw [List.getElem?_eq_getElem (by simpa using Δ.len_pos)] at h0
  have h4 := Option.some.inj h0
  apply h3
  rw [h4]
  simp

end SegJ


open SegJ in
variable (k) in
theorem jSeg : JSeg k := by
  intro Z hZ Δ
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hterm : ∀ a, (Δ.term a).1 = Δ.d := fun _ => rfl
  refine ⟨?_, fun S hS hne => ?_⟩
  · rw [jmL_seg hA hZ Δ _ (fun w hw => by rw [List.mem_ofFn] at hw; obtain ⟨a, rfl⟩ := hw; rfl) List.length_ofFn, if_pos rfl]
  · rw [jmL_seg hA hZ Δ _ ?_ ?_, if_neg (vWord_ne hA Δ S hS hne)]
    · intro w hw
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
      rfl
    · simp [vWord]
      rw [← List.length_eq_length_filter_add]
      simp

end CompanionTheory.Groth

end
end

