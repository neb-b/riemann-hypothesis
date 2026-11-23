module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlmostNormEtaProdEqNegOne
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

open NumberField IsDedekindDomain in
private theorem linearIndependent_one_of_notMem_range {K L : Type} [Field K] [Field L] [Algebra K L]
    {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) : LinearIndependent K ![(1 : L), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [map_zero, zero_mul, add_zero, map_eq_zero] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply hθ
    refine ⟨-s / t, ?_⟩
    have ht' : algebraMap K L t ≠ 0 := (map_ne_zero _).mpr ht
    rw [map_div₀, map_neg, div_eq_iff ht']
    linear_combination -hst

open NumberField IsDedekindDomain in
private theorem exists_basis_one_sqrt_nonsquare_of_finrank_two (K L : Type) [Field K] [CharZero K] [Field L]
    [Algebra K L] (h2 : Module.finrank K L = 2) :
    ∃ (e : Module.Basis (Fin 2) K L) (δ : K), e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ ∧
      ¬ IsSquare δ := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
    by_contra hcon
    push_neg at hcon
    have hbot : (⊥ : Subalgebra K L) = ⊤ :=
      eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr (hcon x)
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
    omega
  let B := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_notMem_range hθ)
    (by simp [h2])
  have hB : ∀ i, B i = ![(1 : L), θ] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hθθ : θ * θ = algebraMap K L (B.repr (θ * θ) 0) +
      algebraMap K L (B.repr (θ * θ) 1) * θ := by
    conv_lhs => rw [← B.sum_repr (θ * θ)]
    rw [Fin.sum_univ_two, hB, hB, Algebra.smul_def, Algebra.smul_def]
    simp
  set q := B.repr (θ * θ) 0
  set p := B.repr (θ * θ) 1
  clear_value p q
  have hθ' : θ - algebraMap K L (p / 2) ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    exact hθ ⟨c + p / 2, by rw [map_add (f := _), hc]; ring⟩
  have hp2 : algebraMap K L (p / 2) * 2 = algebraMap K L p := by
    rw [← map_ofNat (algebraMap K L) 2, ← map_mul, div_mul_cancel₀ p two_ne_zero]
  have hδeq : algebraMap K L (q + p ^ 2 / 4) = algebraMap K L q + algebraMap K L (p / 2) ^ 2 := by
    rw [show q + p ^ 2 / 4 = q + (p / 2) ^ 2 by ring, map_add (f := _), map_pow]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_notMem_range hθ')
    (by simp [h2]), q + p ^ 2 / 4, ?_, ?_, ?_⟩
  · simp [coe_basisOfLinearIndependentOfCardEqFinrank]
  · simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [hδeq]
    linear_combination hθθ - θ * hp2
  · rintro ⟨c, hc⟩
    have hsq : (θ - algebraMap K L (p / 2) - algebraMap K L c) *
        (θ - algebraMap K L (p / 2) + algebraMap K L c) = 0 := by
      have hc' := congrArg (algebraMap K L) hc
      rw [hδeq, map_mul] at hc'
      linear_combination hθθ - θ * hp2 + hc'
    rcases mul_eq_zero.mp hsq with h | h
    · exact hθ' ⟨c, by linear_combination -h⟩
    · exact hθ' ⟨-c, by rw [map_neg]; linear_combination -h⟩

open NumberField IsDedekindDomain in
private theorem exists_sq_sub_mul_sq_of_isSquare {K : Type} [Field K] [CharZero K] {d : K}
    (hd : d ≠ 0) (hsq : IsSquare d) (x : K) : ∃ a b : K, x = a ^ 2 - d * b ^ 2 := by
  obtain ⟨c, rfl⟩ := hsq
  have hc : c ≠ 0 := by rintro rfl; simp at hd
  refine ⟨(x + 1) / 2, (x - 1) / (2 * c), ?_⟩
  field_simp
  ring

open NumberField IsDedekindDomain in
private theorem exists_place_notMem_not_isSquare (F : Type) [Field F] [NumberField F] (δ : F)
    (hδ0 : δ ≠ 0) (hδ : ¬ IsSquare δ) (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) := by
  classical
  by_contra hcon
  push_neg at hcon
  set d : Fˣ := Units.mk0 δ hδ0 with hd
  have hidx := (_root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F δ S₀ hδ0).1
  haveI : (_root_.GlobalTheory.QNorm.locNorm F δ S₀).FiniteIndex := ⟨hidx⟩
  haveI := Fintype.ofFinite (Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀)
  let X : Finset Fˣ := insert d
    (Finset.univ.image fun q : Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀ => q.out)
  obtain ⟨S₁, -, hS₁⟩ := _root_.GlobalTheory.QNorm.exists_superset_mem_sUnits F X S₀
  obtain ⟨S, hS₁S, hadm⟩ := _root_.GlobalTheory.QNorm.exists_admissible_superset_finite_places F (S₁ ∪ S₀)
  have hmem : ∀ x ∈ X, x ∈ _root_.GlobalTheory.QNorm.sUnits F S :=
    hS₁ S (Finset.union_subset_left hS₁S)
  have hdδ : (d : F) = δ := rfl
  refine _root_.GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top F d S hadm (hmem d (Finset.mem_insert_self _ _))
    (by rwa [hdδ]) ?_
  have hle : _root_.GlobalTheory.QNorm.locNorm F δ S₀ ≤ _root_.GlobalTheory.QNorm.locNorm F (d : F) S := by
    intro x hx
    rw [hdδ]
    unfold _root_.GlobalTheory.QNorm.locNorm at hx ⊢
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hx ⊢
    refine ⟨fun v hv => ?_, hx.2⟩
    by_cases hv0 : v ∈ S₀
    · exact hx.1 v hv0
    · rw [_root_.GlobalTheory.QNorm.mem_normSub]
      haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F _).injective
      exact exists_sq_sub_mul_sq_of_isSquare ((map_ne_zero _).mpr hδ0) (hcon v hv0) _
  rw [eq_top_iff]
  intro t _
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.QNorm.locNorm F δ S₀) t
  have ht : t = (QuotientGroup.mk t : Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀).out * (h : Fˣ)⁻¹ := by
    rw [hh]; group
  rw [ht]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hmem _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))
    (Subgroup.mem_sup_right (hle (Subgroup.inv_mem _ h.2)))


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.QuadSymbol.exists_almostNorm_etaProd_eq_neg_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L],
      ∃ (x : _root_.GlobalTheory.QuadSymbol.FinFam K) (y : _root_.GlobalTheory.QuadSymbol.InfFam K),
        _root_.GlobalTheory.QuadSymbol.AlmostNorm K L x ∧ _root_.GlobalTheory.QuadSymbol.etaProd K L x y = -1 := by
  intro K L _ _ _ _ _ _
  classical
  obtain ⟨e, δ, he0, he1, hδ⟩ := exists_basis_one_sqrt_nonsquare_of_finrank_two K L
    (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ ⟨0, by simp⟩
  obtain ⟨v, -, hv⟩ := exists_place_notMem_not_isSquare K δ hδ0 hδ ∅
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.QNorm.exists_local_nonnorm K v _
    ((map_ne_zero _).mpr hδ0) hv
  have hnot : Units.mk0 x hx0 ∉ _root_.GlobalTheory.QuadSymbol.normGroup K L (v.adicCompletion K) := by
    rw [_root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form e he0 he1]
    exact hx
  refine ⟨Pi.mulSingle v (Units.mk0 x hx0), 1, ?_, ?_⟩
  · unfold _root_.GlobalTheory.QuadSymbol.AlmostNorm
    refine (Set.finite_singleton v).subset fun v' hv' => ?_
    by_contra hne
    apply hv'
    rw [Pi.mulSingle_eq_of_ne (Set.mem_singleton_iff.not.mp hne)]
    exact Subgroup.one_mem _
  · unfold _root_.GlobalTheory.QuadSymbol.etaProd
    rw [finprod_eq_single _ v]
    · rw [Pi.mulSingle_eq_same, _root_.GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.mpr hnot,
        Finset.prod_eq_one, mul_one]
      intro w _
      exact _root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr (Subgroup.one_mem _)
    · intro v' hv'
      rw [Pi.mulSingle_eq_of_ne hv']
      exact _root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr (Subgroup.one_mem _)

end GlobalTheory.QuadSymbol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeClasses
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lat_of_coset {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : J ≤ KO k _) {a b : GL (n ⊕ Fin c) k}
    (h : DoubleCoset.mk (R k n c 1) J a = DoubleCoset.mk (R k n c 1) J b) :
    ∃ r ∈ R k n c 1, latOf b = latOf (r * a) := by
  obtain ⟨r, hr, w, hw, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 h
  exact ⟨r, hr, by rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ hw)), mul_one]⟩

variable [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
  (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
  (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
  (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x)
  (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
  (hJ : ∀ j c h, (T.lev j c h).J ≤ KO k (X j ⊕ Fin c))

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem lat_bas {j c h} (g : GL (X j ⊕ Fin c) k) : latOf (g * T.bas j c h) = latOf g := by
  rw [latOf_mul_congr _ (hb j c h), mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem normal_one (c : ℕ) (h : 0 + c = s) : IsNormalRep T ϖ 0 c h 1 := by
  refine ⟨0, 0, fun i => by simp, fun i => zero_mem _, ?_⟩
  rw [lat_bas hb]
  ext y
  simp [mem_normal, mem_latOf_one, mem_pow_zero]

include hϖ hψ hb hs hp hJ

theorem exists_normal {A : RepFam k s X} (hA : T.IsRepSystem A ψ ν) (j : ℕ) :
    ∀ c h, ∀ g ∈ A j c h, ∃ r ∈ R k (X j) (c + 1) 1, IsNormalRep T ϖ j c h (r * g) := by
  induction j with
  | zero =>
    intro c h g hg
    rw [hA.zero] at hg
    obtain rfl : g = 1 := hg
    exact ⟨1, one_mem _, by rw [one_mul]; exact normal_one hb c h⟩
  | succ j ih =>
    intro c h g' hg'
    obtain ⟨g, hg, a, ha, hf⟩ := Set.mem_iUnion₂.1 ((hA.bij j c h).mapsTo hg')
    obtain ⟨r, hr, e', z', he', hz', hl⟩ := ih _ _ g hg
    rw [lat_bas hb, ← nfBasis_one] at hl
    obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c ψ ν _ _ g a hf r hr)
    obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ hψ he' hz'
      (hl ▸ om_supp (hs _ _ _) (r * g) a) (hl ▸ om_per hϖ (hp _ _ _) (r * g) a) h0
    obtain ⟨r₃, hr₃, hl₃⟩ := lat_of_coset (hJ _ _ _) ha
    refine ⟨r₂ * r₃⁻¹, mul_mem hr₂ (inv_mem hr₃), e, z, he, hz, ?_⟩
    rw [lat_bas hb, latOf_mul_congr _ hl₃, ← hl₂]
    congr 1
    group

end GlobalTheory.LatClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymmetricPositionLevelShapeOnParabolicStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionLevel_shape_on_parabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ)
      (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)),
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P →
        (∀ u ∈ N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * embX l γ ∈ P.J →
          ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧
        (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb →
          IsUpperUnip Fin.val gb.val → ∃ hm : embX l γ ∈ P.J,
          (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧
        ∀ u ∈ N k (Fin κ) l 1, ∀ hm : u ∈ P.J,
          (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u) := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP
  have block_mul_embX {F : Type} [Field F] {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F}
      (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
      (u * embX l γ).val.toBlocks₁₁ = γ.val := by
    rw [Units.val_mul, GlobalTheory.RootEx.Radical.embX_val, ← Matrix.fromBlocks_toBlocks u.val,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁,
      GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu]
    simp
  have simpleSum_embX (γ : GL (Fin κ) k) : simpleSum (embX l γ) = 0 := by
    apply GlobalTheory.RootEx.Radical.simpleSum_eq_zero
    intro i j
    rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.fromBlocks_apply₂₂]
  refine ⟨?_, ?_, ?_⟩
  · intro u hu γ hm
    obtain ⟨u', hu', γ', hγ', g₀, hg₀, hr₀⟩ := (hP.1 _).1 hm
    have map_corner {F : Type} [Field F] (f : 𝒪[k] →+* F)
        (x : GL (Fin κ ⊕ Fin l) F) (y : GL (Fin κ) F)
        (hx : Matrix.GeneralLinearGroup.map f g₀ = x) (hy : x.val.toBlocks₁₁ = y.val) :
        (g₀.val.toBlocks₁₁).map f = y.val := by
      rw [← hy, ← hx]
      rfl
    have hBk := map_corner (algebraMap 𝒪[k] k) _ γ hg₀ (block_mul_embX hu γ)
    have hBr := map_corner (IsLocalRing.residue 𝒪[k]) _ γ' hr₀ (block_mul_embX hu' γ')
    have hdet : IsUnit (g₀.val.toBlocks₁₁).det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      change ((g₀.val.toBlocks₁₁).map (IsLocalRing.residue 𝒪[k])).det ≠ 0
      rw [hBr]
      exact (Matrix.isUnits_det_units γ').ne_zero
    refine ⟨γ', ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩, hγ'⟩
    · exact Units.ext (by rw [← hBk]; rfl)
    · exact Units.ext (by rw [← hBr]; rfl)
  · intro γ gb hred hgb
    obtain ⟨γ₀, h₁, h₂⟩ := hred
    let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
      ⟨Matrix.fromBlocks γ₀.val 0 0 1, Matrix.fromBlocks (γ₀⁻¹).val 0 0 1,
        by rw [Matrix.fromBlocks_multiply]; simp, by rw [Matrix.fromBlocks_multiply]; simp⟩
    have hemb {F : Type} [Field F] (f : 𝒪[k] →+* F) :
        Matrix.GeneralLinearGroup.map f g₀ = embX l (Matrix.GeneralLinearGroup.map f γ₀) := by
      refine Units.ext ?_
      rw [GlobalTheory.RootEx.Radical.embX_val]
      change (Matrix.fromBlocks γ₀.val 0 0 1).map f = _
      rw [Matrix.fromBlocks_map]
      simp
    have hm : embX l γ ∈ P.J :=
      (hP.1 _).2 ⟨1, one_mem _, gb, hgb, g₀, by rw [hemb, h₁], by rw [hemb, h₂, one_mul]⟩
    refine ⟨hm, ?_⟩
    have hblk : (embX l γ).val.toBlocks₁₁ = γ.val := by
      rw [GlobalTheory.RootEx.Radical.embX_val, Matrix.toBlocks_fromBlocks₁₁]
    rw [hP.2 ⟨_, hm⟩]
    simp only [simpleSum_embX, hblk, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
  · intro u hu hm
    rw [hP.2 ⟨u, hm⟩]
    simp only [GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu, GlobalTheory.GenericShape.superSum_one,
      mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]
end

