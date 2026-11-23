module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0066

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MultOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckSingleMultiplication

section Ring

theorem mulR_sg_left (a : IrrGL (k := k)) (b : GrothGL k) :
    mulR (sg a) b = b.sum fun y n => n • cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep y)) := by
  unfold mulR sg
  rw [Finsupp.sum_single_index]
  · simp only [one_mul]
  · simp

theorem mulR_sg_zero (a : IrrGL (k := k)) : mulR (sg a) 0 = 0 := by
  rw [mulR_sg_left, Finsupp.sum_zero_index]

theorem mulR_sg_add (a : IrrGL (k := k)) (b c : GrothGL k) : mulR (sg a) (b + c) = mulR (sg a) b + mulR (sg a) c := by
  simp only [mulR_sg_left]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem mulR_sg_zsmul (a : IrrGL (k := k)) (n : ℤ) (b : GrothGL k) : mulR (sg a) (n • b) = n • mulR (sg a) b :=
  (AddMonoidHom.mk' (mulR (sg a)) (mulR_sg_add a)).map_zsmul n b

theorem sum_single_one_smul (T : IrrGL (k := k) → GrothGL k) (b : IrrGL (k := k)) :
    (Finsupp.single b (1 : ℤ)).sum (fun y n => n • T y) = T b := by
  rw [Finsupp.sum_single_index] <;> simp

theorem mulR_sg_sg (a b : IrrGL (k := k)) : mulR (sg a) (sg b) = cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep b)) := by
  rw [mulR_sg_left]
  exact sum_single_one_smul (fun y => cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep y))) b

theorem mulR_sg_left_comm (ha : Assoc k) (hc : Comm k) (a b : IrrGL (k := k)) (c : GrothGL k) :
    mulR (sg a) (mulR (sg b) c) = mulR (sg b) (mulR (sg a) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [mulR_sg_zero]
  | add f g hf hg => rw [mulR_sg_add, mulR_sg_add, hf, hg, mulR_sg_add, mulR_sg_add]
  | single z n =>
    have hs : Finsupp.single z n = n • sg z := by simp [sg]
    rw [hs, mulR_sg_zsmul, mulR_sg_zsmul, mulR_sg_zsmul, mulR_sg_zsmul, ← ha a b z, mulR_sg_sg a b,
      hc a b, ← mulR_sg_sg b a, ha b a z]

theorem foldr_perm (ha : Assoc k) (hc : Comm k) {l₁ l₂ : List (IrrGL (k := k))} (p : l₁.Perm l₂) (u : GrothGL k) :
    l₁.foldr (fun y a => mulR (sg y) a) u = l₂.foldr (fun y a => mulR (sg y) a) u := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l => simp only [List.foldr_cons]; exact mulR_sg_left_comm ha hc y x _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end Ring

theorem jordan_holder_mult_eq_of_class (y : IrrGL (k := k)) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin y.1) k) V) (π' : Representation ℂ (GL (Fin y.1) k) W)
    (hπ : HasFiniteLength π) (hπ' : HasFiniteLength π') (h : cl0 π = cl0 π') :
    jhMult (IrrGL.rep y) π = jhMult (IrrGL.rep y) π' := by
  have e1 : cl0 π = clsGL π hπ := by unfold cl0; rw [dite_eq_left hπ]
  have e2 : cl0 π' = clsGL π' hπ' := by unfold cl0; rw [dite_eq_left hπ']
  have h2 := congrArg (fun a : GrothGL k => a ⟨y.1, y.2⟩) (e1.symm.trans (h.trans e2))
  simp only [clsGL_apply, cls_apply] at h2
  have h3 : (jhMult (IrrGL.rep y) π).toNat = (jhMult (IrrGL.rep y) π').toNat := by exact_mod_cast h2
  rw [← ENat.natCast_toNat (jhMult_ne_top y.2.rep.irr hπ), ← ENat.natCast_toNat (jhMult_ne_top y.2.rep.irr hπ'), h3]

theorem jhMult_mul_jm_le {g N : ℕ} (z : Fin g → IrrGL (k := k)) (hz : ∑ b, (z b).1 = N) {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (τ : Representation ℂ (GL (Fin N) k) W) (hπ : IsSmooth π) :
    jhMult τ π * jm z hz τ ≤ jm z hz π := by
  have hadd : ∀ S T : Subrepresentation π, T ≤ S →
      jm z hz T.toRepresentation + jm z hz (subQuot S T) ≤ jm z hz S.toRepresentation := by
    intro S T h
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hS : IsSmooth S.toRepresentation :=
      (IsSubquotient.of_injective (⟨S.toSubmodule.subtype, fun _ => rfl⟩ :
        S.toRepresentation.IntertwiningMap π) Subtype.val_injective).isSmooth hπ
    refine GlobalTheory.CompanionTheory.CsStages.jhMult_add_le (jacMap _ ι) (jacMap _ p)
      (GlobalTheory.JacquetExact.jacMap_injective _ hS ι (Submodule.inclusion_injective h))
      (GlobalTheory.JacquetExact.jacMap_surjective _ p (Submodule.Quotient.mk_surjective _)) fun u => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : p (ι v) = 0 := (Submodule.Quotient.mk_eq_zero _).2 v.2
    show Submodule.Quotient.mk (p (ι v)) = 0
    rw [this]
    rfl
  have h := GlobalTheory.CompanionTheory.CsStages.jhMult_mul_le_of_steps τ π (fun S => jm z hz S.toRepresentation) (jm z hz τ)
    (fun S T h => le_trans le_self_add (hadd S T h))
    (fun S T h ⟨φ⟩ => by
      have := hadd S T h
      rwa [GlobalTheory.T.jacquet_multiplicity_of_equiv z hz _ _ ⟨φ⟩] at this)
  rwa [GlobalTheory.T.jacquet_multiplicity_of_equiv z hz _ _ ⟨topEquiv π⟩] at h

theorem ofFn_perm {α : Type*} {h : ℕ} (x : Fin h → α) (σ : Equiv.Perm (Fin h)) :
    (List.ofFn (x ∘ σ)).Perm (List.ofFn x) := by
  exact Equiv.Perm.ofFn_comp_perm σ x

theorem jhMult_le_one_of_equiv (y : IrrGL (k := k)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin y.1) k) V} {g : ℕ} {z : Fin g → IrrGL (k := k)} {hz : ∑ b, (z b).1 = y.1}
    (hsoc : IsSocle (IrrGL.rep y) π) (e : π.Equiv (prodIrr z hz)) (hjm : jm z hz (prodIrr z hz) ≤ 1) :
    jhMult (IrrGL.rep y) π ≤ 1 := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨hirr, f, hf, -⟩ := hsoc
  have hnt := nontrivial_of_irreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.2.rep.V)
  have hpos : 1 ≤ jm z hz (IrrGL.rep y) :=
    GlobalTheory.T.jacquet_multiplicity_pos hA z hz (IrrGL.rep y) y.2.rep.smooth (e.toIntertwiningMap.comp f)
      ⟨v, fun h0 => hv (hf (e.injective (by simpa using h0)))⟩
  have hle := jhMult_mul_jm_le z hz (prodIrr z hz) (IrrGL.rep y) (isSmooth_prodIrr z hz)
  rw [jhMult_congr_right _ e]
  exact (le_mul_of_one_le_right' hpos).trans (hle.trans hjm)

theorem jhMult_rev_le_one (c : Cls k) (_𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL (k := k)) (y : IrrGL (k := k))
    (Δ : Fin h → Segment k) (hΔo : ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) (hΔL : ∀ i, IsLSeg (Δ i) (x i).rep)
    (hdr : ∑ a, (x (Fin.rev a)).1 = y.1) (hsoc : IsSocle (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr)) :
    jhMult (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr) ≤ 1 := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hΓ : IsRevOrdered (Δ ∘ Fin.rev) := fun i j hij => hΔo (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.2 hij)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order (Δ ∘ Fin.rev)
  have hσr := _root_.GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon _ hσ
  have hdrs : ∑ a, ((x ∘ Fin.rev) (σ a)).1 = y.1 := by
    rw [← hdr]; exact Equiv.sum_comp σ (fun a => ((x ∘ Fin.rev) a).1)
  obtain ⟨e1⟩ := GlobalTheory.T.reverse_ordered_product_perm_equiv hA c.com (Δ ∘ Fin.rev) σ (x ∘ Fin.rev) hdr hdrs hΓ hσr (fun i => hΔL (Fin.rev i))
  obtain ⟨g, z, hz, ⟨e2⟩, hjm⟩ :=
    GlobalTheory.T.canonical_product_equiv_multiplicity_one hA c.jac c.unl ((Δ ∘ Fin.rev) ∘ σ) ((x ∘ Fin.rev) ∘ σ) hdrs hσ (fun i => hΔL (Fin.rev (σ i)))
  have e : (prodIrr (x ∘ Fin.rev) hdr).Equiv (prodIrr z hz) := e1.trans e2
  exact jhMult_le_one_of_equiv y hsoc e hjm

end GrothendieckSingleMultiplication

open GrothendieckSingleMultiplication in
variable (k) in
theorem multOne (c : Cls k) (_hm : MulCls k) (ha : Assoc k) (hc : Comm k) (_h1 : One k) (hl : ProdList k) :
    MultOne k := by
  intro 𝔪 h x y hd hx hy
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨Δ, ⟨hΔm, hΔo⟩, hΔL⟩ := hx
  have hdr : ∑ a, (x (Fin.rev a)).1 = y.1 := by
    rw [← hd]; exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc : IsSocle (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr) :=
    by have hs := c.soc; unfold LSocleGL at hs; exact hs 𝔪 h y.1 x hdr ⟨Δ, ⟨hΔm, hΔo⟩, hΔL⟩ (IrrGL.rep y) hy
  have hcl : cl0 (prodIrr x hd) = cl0 (prodIrr (x ∘ Fin.rev) hdr) := by
    rw [hl h y.1 x hd, hl h y.1 (x ∘ Fin.rev) hdr]
    exact foldr_perm ha hc (ofFn_perm x Fin.revPerm).symm _
  rw [jordan_holder_mult_eq_of_class y _ _ (GlobalTheory.T.product_irreducible_finite_length hA x hd) (GlobalTheory.T.product_irreducible_finite_length hA (x ∘ Fin.rev) hdr) hcl]
  exact le_antisymm (jhMult_rev_le_one c 𝔪 x y Δ hΔo hΔL hdr hsoc)
    (Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 hsoc.isSubquotient))

end CompanionTheory.Groth
end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PhiZAux
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.GrothendieckPhiBijection

theorem interleave_perm {T : Type*} {u v w : List T} (h : Zc.Comb.Interleave u v w) : w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem shuffle_perm {T : Type*} {us : List (List T)} {w : List T} (h : Zc.Comb.Shuffle us w) :
    w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih => rw [List.flatten_cons]; exact (interleave_perm hi).trans (ih.append_left _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_decW (Γ : Segment k) : ((decW Γ : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = Γ.ms := by
  rw [decW, Segment.ms, ← Fin.univ_val_map]
  have : (fun i : Fin Γ.len => Γ.term i.rev) = Γ.term ∘ (Fin.revPerm : Equiv.Perm (Fin Γ.len)) := rfl
  rw [this, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = msupp (L : Multiset (Segment k)) := by
  induction L with
  | nil => simp [msupp]
  | cons Γ L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, coe_decW, ← Multiset.cons_coe, msupp, msupp,
      Multiset.cons_bind]

theorem coe_eq_msupp_of_inShW {𝔫 : Multiset (Segment k)} {w : List (IrrGL (k := k))} (h : InShW 𝔫 w) :
    (w : Multiset (IrrGL (k := k))) = msupp 𝔫 := by
  obtain ⟨L, rfl, hL⟩ := h
  rw [Multiset.coe_eq_coe.2 (shuffle_perm hL), coe_flatten_decW]

theorem msupp_eq_of_isL (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) {𝔫 : Multiset (Segment k)}
    {x : IrrGL (k := k)} (hx : IsL 𝔫 x.rep) (w : List (IrrGL (k := k))) (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd x.rep w) :
    (w : Multiset (IrrGL (k := k))) = msupp 𝔫 := by
  obtain ⟨h, y, hd, ⟨Δ, hΔ, hL⟩, hcos⟩ := hx
  have h1 : Wd (prodIrr y hd) w := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr y hd) hcos.isSubquotient w hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hj y hd Δ hL w hc h1
  rw [hΔ.1] at h2
  exact coe_eq_msupp_of_inShW h2

theorem wd_of_jmL_eq_one {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {w : List (IrrGL (k := k))} (h : jmL w π = 1) : Wd π w := by
  unfold jmL at h
  split_ifs at h with hd
  · exact ⟨hd, by rw [h]; exact one_ne_zero⟩
  · exact absurd h zero_ne_one

theorem msupp_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) (hS : JSeg k) (Δ : Segment k)
    {𝔫 : Multiset (Segment k)} (h𝔫 : IsL 𝔫 (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL (k := k)))) : msupp 𝔫 = Δ.ms := by
  have hc : ∀ c ∈ List.ofFn Δ.term, c.IsCusp := by
    intro c hc
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hc
    exact Δ.isCusp_term a
  have := msupp_eq_of_isL hA hj h𝔫 (List.ofFn Δ.term) hc (wd_of_jmL_eq_one (hS Z hZ Δ).1)
  rw [← this, Segment.ms, Fin.univ_val_map]

theorem seg_eq_of_ms_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Γ Δ : Segment k} (h : Γ.ms = Δ.ms) : Γ = Δ := by
  have hlen : Γ.len = Δ.len := by rw [← Segment.card_ms, h, Segment.card_ms]
  have mem_first : ∀ D : Segment k, D.first ∈ D.ms := fun D =>
    Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, D.len_pos, by simp⟩)
  have hΓ : Γ.first ∈ Δ.ms := by rw [← h]; exact mem_first Γ
  have hΔ : Δ.first ∈ Γ.ms := by rw [h]; exact mem_first Δ
  obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hΓ)
  obtain ⟨b, -, hb⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hΔ)
  have h0 : Δ.first.nu ((a + b : ℕ) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ) := by
    rw [Nat.cast_zero, IrrGL.nu_zero, Nat.cast_add, ← IrrGL.nu_nu, ha, hb]
  have hab := GlobalTheory.T.cuspidal_twist_injective hA Δ.first Δ.isCusp_first _ _ h0
  have ha0 : a = 0 := by omega
  subst ha0
  refine Segment.ext_first ?_ hlen
  rw [← ha]
  simp

theorem len_lt_of_msupp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} {M : Multiset (Segment k)}
    (hM : msupp M = Δ.ms) (hne : M ≠ {Δ}) : ∀ Γ ∈ M, Γ.len < Δ.len := by
  intro Γ hΓ
  have hle : Γ.ms ≤ Δ.ms := by rw [← hM]; exact Multiset.le_bind M hΓ
  have hcard := Multiset.card_le_card hle
  rw [Segment.card_ms, Segment.card_ms] at hcard
  refine lt_of_le_of_ne hcard fun heq => hne ?_
  have hms : Γ.ms = Δ.ms := Multiset.eq_of_le_of_card_le hle (by rw [Segment.card_ms, Segment.card_ms, heq])
  have hΓΔ := seg_eq_of_ms_eq hA hms
  obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem hΓ
  have h2 : msupp M' = 0 := by
    have h3 : Γ.ms + msupp M' = Δ.ms := by rw [← hM, msupp, msupp, Multiset.cons_bind]
    rw [hms] at h3
    simpa using h3
  have h3 : M' = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun Γ' hΓ' => ?_
    have h4 : Γ'.ms ≤ msupp M' := Multiset.le_bind M' hΓ'
    rw [h2, Multiset.le_zero] at h4
    have h5 := congrArg Multiset.card h4
    rw [Segment.card_ms, Multiset.card_zero] at h5
    exact Γ'.len_pos.ne' h5
  rw [h3, hΓΔ, Multiset.cons_zero]

theorem toMultiset_eq_single_iff (s : Segment k →₀ ℕ) (Δ : Segment k) :
    Finsupp.toMultiset s = {Δ} ↔ s = Finsupp.single Δ 1 := by
  classical
  constructor
  · intro h
    calc s = Multiset.toFinsupp (Finsupp.toMultiset s) := (Finsupp.toMultiset_toFinsupp s).symm
      _ = Multiset.toFinsupp (Finsupp.toMultiset (Finsupp.single Δ 1)) := by
          rw [h, Finsupp.toMultiset_single, one_nsmul]
      _ = Finsupp.single Δ 1 := Finsupp.toMultiset_toFinsupp _
  · rintro rfl
    rw [Finsupp.toMultiset_single, one_nsmul]

theorem prod_X_of_map (s : Segment k →₀ ℕ) {h : ℕ} (Γ : Fin h → Segment k)
    (hΓ : Finset.univ.val.map Γ = Finsupp.toMultiset s) :
    ∏ a, (MvPolynomial.X (Γ a) : MvPolynomial (Segment k) ℤ) = MvPolynomial.monomial s 1 := by
  classical
  have h1 : (Finset.univ.val.map fun a => (MvPolynomial.X (Γ a) : MvPolynomial (Segment k) ℤ)) =
      (Finset.univ.val.map Γ).map MvPolynomial.X := by
    rw [Multiset.map_map]; rfl
  rw [Finset.prod_eq_multiset_prod, h1, hΓ, Finset.prod_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp only [Finsupp.count_toMultiset]
  exact MvPolynomial.prod_X_pow_eq_monomial

theorem exists_enum (s : Segment k →₀ ℕ) :
    ∃ (h : ℕ) (Γ : Fin h → Segment k), Finset.univ.val.map Γ = Finsupp.toMultiset s :=
  ⟨(Finsupp.toMultiset s).toList.length, fun a => (Finsupp.toMultiset s).toList.get a, by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩

def Jh (W : List (IrrGL (k := k))) : GrothGL k →+ ℤ where
  toFun := J W
  map_zero' := Finsupp.sum_zero_index
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def ell (Δ : Segment k) : GrothGL k →+ ℤ := ∑ S ∈ vSets Δ, (-1 : ℤ) ^ S.card • Jh (vWord Δ S)

theorem ell_apply (Δ : Segment k) (a : GrothGL k) :
    ell Δ a = ∑ S ∈ vSets Δ, (-1 : ℤ) ^ S.card * J (vWord Δ S) a := by
  simp only [ell, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul]
  rfl

theorem J_sg (W : List (IrrGL (k := k))) (x : IrrGL (k := k)) : J W (sg x) = ((jmL W x.rep).toNat : ℤ) := by
  unfold J sg
  rw [Finsupp.sum_single_index (zero_mul _), one_mul]

theorem vWord_empty (Δ : Segment k) : vWord Δ ∅ = List.ofFn Δ.term := by
  simp [vWord, List.ofFn_eq_map]

theorem cusp_vWord (Δ : Segment k) (S : Finset (Fin Δ.len)) : ∀ w ∈ vWord Δ S, w.IsCusp := by
  intro w hw
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
  exact Δ.isCusp_term a

theorem ell_sg {Δ : Segment k} {x : IrrGL (k := k)} (h1 : jmL (List.ofFn Δ.term) x.rep = 1)
    (h0 : ∀ S ∈ vSets Δ, S ≠ ∅ → jmL (vWord Δ S) x.rep = 0) : ell Δ (sg x) = 1 := by
  rw [ell_apply, Finset.sum_eq_single (∅ : Finset (Fin Δ.len))]
  · rw [J_sg, vWord_empty, h1]; simp
  · intro S hS hne; rw [J_sg, h0 S hS hne]; simp
  · intro h; exact absurd (by simp [vSets]) h


open Classical in
theorem ell_prod (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL (k := k)) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep) (Δ : Segment k) {h N : ℕ}
    (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N) :
    ell Δ (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) =
      if Finset.univ.val.map Γ = {Δ} then (-1) ^ (Δ.len - 1) else 0 := by
  have := hAlt Δ h Γ
  rw [ell_apply]
  convert this using 1
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [(hJ (vWord Δ S) N _ (prodIrr (fun a => Lseg (Γ a)) hd) (isSmooth_prodIrr _ hd)
      (GlobalTheory.T.product_irreducible_finite_length hA _ hd)).2,
    GlobalTheory.T.segment_product_jacquet_shuffle_count hA hj Γ (fun a => Lseg (Γ a)) hd (fun i => hL (Γ i)) (vWord Δ S) (cusp_vWord Δ S)]
  simp

theorem vars_lt (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} (p : MvPolynomial (Segment k) ℤ)
    (hp : ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = Δ.ms) :
    ∀ t ∈ (p - MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1))).vars, t.len < Δ.len := by
  classical
  intro t ht
  obtain ⟨d, hd, htd⟩ := (MvPolynomial.mem_vars_iff_mem_support t).1 ht
  have hcd := MvPolynomial.mem_support_iff.1 hd
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial] at hcd
  have hde : d ≠ Finsupp.single Δ 1 := by
    rintro rfl
    simp at hcd
  rw [if_neg (Ne.symm hde), sub_zero] at hcd
  have hne : Finsupp.toMultiset d ≠ {Δ} := fun h => hde ((toMultiset_eq_single_iff d Δ).1 h)
  exact len_lt_of_msupp hA (hp d (MvPolynomial.mem_support_iff.2 hcd)) hne t ((Finsupp.mem_toMultiset d t).2 htd)

end CompanionTheory.Groth.GrothendieckPhiBijection

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriCoeFlattenDecW
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

section TriLemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tri_coe_decW (Δ : Segment k) : ((decW Δ : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = Δ.ms := by
  have e := GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn Δ.term
  rw [decW, ← e, Multiset.coe_reverse, Segment.ms, Fin.univ_val_map]

theorem tri_coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL (k := k))) : Multiset (IrrGL (k := k))) = (L : Multiset (Segment k)).bind Segment.ms := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe,
      Multiset.cons_bind]

theorem tri_msupp_of_inShW {𝔪 : Multiset (Segment k)} {w : List (IrrGL (k := k))} (H : InShW 𝔪 w) :
    msupp 𝔪 = (w : Multiset (IrrGL (k := k))) := by
  obtain ⟨L, rfl, hS⟩ := H
  rw [msupp, ← tri_coe_flatten_decW]
  exact (Multiset.coe_eq_coe.2 (GlobalTheory.T.perm_flatten_of_shuffle _ _ hS)).symm

theorem tri_msupp_wtW {h : ℕ} {Γ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Γ 𝔫) :
    msupp 𝔫 = (wtW Γ : Multiset (IrrGL (k := k))) := by
  have e : wtW Γ = (((List.ofFn Γ).reverse).map decW).flatten := by
    rw [wtW, GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, List.map_ofFn]
    try rfl
  rw [e, tri_coe_flatten_decW, Multiset.coe_reverse, ← Fin.univ_val_map, H.1, msupp]

theorem tri_sqLen_map_toA (𝔪 : Multiset (Segment k)) : Comb.sqLen (𝔪.map toA) = sq 𝔪 := by
  rw [Comb.sqLen, Multiset.map_map]
  rfl

end TriLemmas

theorem tri (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Cls k) :
    Tri k := by
  intro 𝔪 𝔫 h x y hd hx hy hm
  obtain ⟨Δ, hΔ, hΔL⟩ := hx
  obtain ⟨h', x', hd', ⟨Γ, hΓ, -⟩, -⟩ := id hy
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have w1 : Wd y.rep (wtW Γ) := _root_.GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL hA c.soc c.jac 𝔫 y.rep hy h' Γ hΓ
  have hs : IsSubquotient y.rep (prodIrr x hd) := jhMult_ne_zero_iff.1 hm
  have w2 : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hs _ w1
  have sh : InShW (Finset.univ.val.map Δ) (wtW Γ) :=
    GlobalTheory.T.segment_product_word_in_shuffle hA c.jac x hd Δ hΔL (wtW Γ) (_root_.GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp Γ) w2
  rw [hΔ.1] at sh
  refine ⟨(tri_msupp_of_inShW sh).trans (tri_msupp_wtW hΓ).symm, ?_⟩
  by_cases he : 𝔪 = 𝔫
  · exact Or.inl he
  right
  have hL := GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ
  have hne : 𝔪.map toA ≠ (((List.ofFn Γ).map toA : List _) : Multiset _) := by
    rw [hL]
    intro e
    exact he (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)
  have key := GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic
    ((List.ofFn Γ).map toA) (𝔪.map toA) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ)
    (GlobalTheory.CompanionTheory.ZcWords.inSh_of_inShW sh) hne
  rw [hL, tri_sqLen_map_toA, tri_sqLen_map_toA] at key
  exact key

end CompanionTheory.Groth

end
end

