module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeSelfDualSemicharacterIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumPrincipalTorusAtOrthonormalFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdIterateTwistedConj
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.LKResNrmConj

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem coe_frobQ_iterate (r k : ℕ) (b : Qr p r) :
    (((⇑(frobQ p r))^[k] b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ k) (b : PadicAlgCl p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
    rfl

theorem frobQ_iterate_self (r : ℕ) (hr : 0 < r) (b : Qr p r) : (⇑(frobQ p r))^[r] b = b := by
  refine Subtype.ext ?_
  have hK : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  rw [coe_frobQ_iterate]
  exact (IsFrobOn.pow_fixes_iff p (Q0 p) hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ b.2

theorem sigKQ_iterate_self (r : ℕ) (hr : 0 < r) (y : KQ p K r) : (⇑(sigKQ p K r))^[r] y = y := by
  have ht : ∀ (k : ℕ) (a : K) (b : Qr p r), (⇑(sigKQ p K r))^[k] (inclK p K r a * inclQ p K r b) =
      inclK p K r a * inclQ p K r ((⇑(frobQ p r))^[k] b) := by
    intro k a b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, sigKQ_apply_inclK, sigKQ_apply_inclQ,
        Function.iterate_succ_apply']
  have key : ∀ z : K ⊗[ℚ_[p]] Qr p r, (⇑(sigKQ p K r))^[r] (z : KQ p K r) = (z : KQ p K r) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact iterate_map_zero (sigKQ p K r) r
    | tmul a b =>
      have e : inclK p K r a * inclQ p K r b = (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) := by
        change (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] b) = a ⊗ₜ[ℚ_[p]] b
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have h := ht r a b
      rw [frobQ_iterate_self p r hr, e] at h
      exact h
    | add z w hz hw =>
      exact (iterate_map_add (sigKQ p K r) r (z : KQ p K r) (w : KQ p K r)).trans (congrArg₂ (· + ·) hz hw)
  exact key y

theorem sigRes_iterate_self (n r : ℕ) (hr : 0 < r) (g : GL (Fin n) (KQ p K r)) :
    (⇑(sigRes p K n r))^[r] g = g := by
  have h : ∀ (k : ℕ) (i j : Fin n), ((⇑(sigRes p K n r))^[k] g).val i j = (⇑(sigKQ p K r))^[k] (g.val i j) := by
    intro k i j
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h, sigKQ_iterate_self p K r hr]

end GlobalTheory.LKResNrmConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjAGphiEqSum
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacProj

theorem mem_vset {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (Λ : Formalism.L2.Pj.GenLat E n) (hU : Λ.Unimod) (hfg : Λ.La.FG) : Λ.La ∈ Vset E n 1 := by
  have hU' := (GenLatCmp.unimod_iff Λ.La).1 hU
  obtain ⟨N, hN, h⟩ := TensLat.exists_mul_le (B := stdL E n) (B' := Λ.La)
    (Submodule.fg_span (Set.finite_range _)) (DualFamily.span_eq_top Λ.La hfg fun x => (hU' x).2)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {N}))
  have h4 : ∀ u ∈ stdL E n, ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) • u ∈ Λ.La := fun u hu => by
    have e : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : E) = (a : E) * (N : E) := by
      have := congrArg (algebraMap (𝓞 E) E) ha
      rw [map_mul, map_natCast] at this
      exact this.symm
    rw [e, mul_smul]
    exact TensLat.int_smul_mem a.isIntegral_coe (h u hu)
  refine ⟨hfg, hU', _, Nat.pos_of_ne_zero ?_, Nat.coprime_one_right _,
    GenLatCmp.smul_mem_std hU' h4, h4⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hN

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {w : E} {A A' : AddSubgroup (Matrix (Fin n) (Fin r) E)}

theorem heisG_sum {ι : Type} (y : Matrix (Fin n) (Fin r) E) (s : Finset ι) (f : ι → TF n g) :
    heisG X bas y (∑ i ∈ s, f i) = ∑ i ∈ s, heisG X bas y (f i) := by
  funext x; simp [heisG, heisS, Finset.sum_mul]

theorem rho_eq_iff (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    {a b : Matrix (Fin n) (Fin r) E} (ha : a ∈ A) (hb : b ∈ A) :
    epsW X w a • heisG X bas a v = epsW X w b • heisG X bas b v ↔ -a + b ∈ A' := by
  have hfix : ∀ y, epsW X w y • heisG X bas y v = v ↔ y ∈ A' := by
    refine fun y => ⟨fun h => ?_, hv.2.2 y⟩
    by_contra hy
    have := hA'.ip_eq_zero idx hs hn hv hy
    rw [h, hv.2.1] at this
    exact one_ne_zero this
  rw [← hfix, ← hA.rho_rho idx hs hn (A.neg_mem ha) hb hv.1]
  constructor
  · intro h
    rw [← h, hA.rho_rho idx hs hn (A.neg_mem ha) ha hv.1, neg_add_cancel,
      TensVac.rho_zero idx hs hn hv.1]
  · intro h
    conv_lhs => rw [← h]
    rw [hA.rho_rho idx hs hn ha (A.neg_mem ha) (TensVac.rho_sb idx hs hn b hv.1), add_neg_cancel,
      TensVac.rho_zero idx hs hn (TensVac.rho_sb idx hs hn b hv.1)]

theorem proj_eq (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    (hA : TensVac.Good X w A) (hA' : TensVac.Good X w A') {v : TF n g} (hv : IsVac X bas w A' v)
    (R : Finset (Matrix (Fin n) (Fin r) E)) (hR : ∀ y ∈ R, y ∈ A)
    (hR' : ∀ y ∈ A, ∃! y', y' ∈ R ∧ y - y' ∈ A') :
    R.card = A'.relIndex A ∧
      projA X bas w A v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧
      IsVac X bas w A ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w A v) := by
  set f : Matrix (Fin n) (Fin r) E → TF n g := fun y => epsW X w y • heisG X bas y v with hf
  have hiff : ∀ a ∈ A, ∀ b ∈ A, f a = f b ↔ -a + b ∈ A' := fun a ha b hb =>
    rho_eq_iff idx hs hn hA hA' hv ha hb
  have hinj : Set.InjOn f R := fun a ha b hb h => by
    have h1 := (hiff a (hR a ha) b (hR b hb)).1 h
    rw [neg_add_eq_sub] at h1
    exact (hR' b (hR b hb)).unique ⟨ha, h1⟩ ⟨hb, by rw [sub_self]; exact A'.zero_mem⟩
  have him : f '' A = f '' R := by
    refine Set.Subset.antisymm ?_ (Set.image_mono fun y hy => hR y hy)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, ⟨hb, h⟩, -⟩ := hR' a ha
    exact ⟨b, hb, (hiff b (hR b hb) a ha).2 (by rwa [neg_add_eq_sub])⟩
  have hc : (f '' A).ncard = R.card := by
    rw [him, hinj.ncard_image, Set.ncard_coe_finset]
  have hidx : R.card = A'.relIndex A := hc.symm.trans (TensVac.ncard_image_eq f hiff)
  refine ⟨hidx, ?_, ?_⟩
  · have h1 : ∑ᶠ ψ ∈ f '' R, ψ = ∑ y ∈ R, f y :=
      (finsum_mem_image (f := fun ψ : TF n g => ψ) hinj).trans (finsum_mem_coe_finset _ _)
    rw [projA, ← hf, hc, him, h1]
  · obtain ⟨u, hu, -⟩ := hA.vac hs
    have hov := hA.overlap idx hs hn hA' hu hv
    rw [(hA.proj idx hs hn hv.1 hu).2, smul_smul]
    set a := (Real.sqrt (R.card : ℝ) : ℂ) * SW.ip v u with ha
    have hn1 : ‖a‖ ^ 2 = 1 := by
      rw [ha, TensVac.ip_conj hu.1 hv.1, norm_mul, Complex.norm_conj, Complex.norm_real, mul_pow,
        Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _), hidx, hov]
    refine ⟨TensVac.sb_smul a hu.1, ?_, fun y hy => ?_⟩
    · rw [TensVac.ip_smul_left a hu.1 (TensVac.sb_smul a hu.1), TensVac.ip_smul_right a hu.1 hu.1,
        hu.2.1, _root_.mul_one, Complex.mul_conj']
      exact_mod_cast hn1
    · rw [TensVac.heisG_smul, smul_comm, hu.2.2 y hy]

end

theorem projA_gphi_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ (Λ₀ Λ : Formalism.L2.Pj.GenLat E n), Λ₀.Unimod → Λ.Unimod → Λ₀.La.FG → Λ.La.FG → ∀ v : TF n g, IsVac X bas w (tens Λ₀.La L) v → ∀ R : Finset (Matrix (Fin n) (Fin r) E), (∀ y ∈ R, y ∈ tens Λ.La L) → (∀ y ∈ tens Λ.La L, ∃! y', y' ∈ R ∧ y - y' ∈ tens Λ₀.La L) → R.card = ((Λ.La ⊓ Λ₀.La).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ r ∧ projA X bas w (tens Λ.La L) v = ((R.card : ℂ))⁻¹ • ∑ y ∈ R, epsW X w y • heisG X bas y v ∧ IsVac X bas w (tens Λ.La L) ((Real.sqrt (R.card : ℝ) : ℂ) • projA X bas w (tens Λ.La L) v) ∧ ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E), gphi X bas w Λ.La L v c Y = ((R.card : ℂ))⁻¹ • ∑ q, ∑ y ∈ R, (c q * epsW X w y) • heisG X bas (Y q) (heisG X bas y v) := by
  intro E _ _ _ r g n X bas idx hs hn w hw hw1 L hL Λ₀ Λ hU₀ hU hf₀ hf v hv R hR hR'
  have h₀ := mem_vset Λ₀ hU₀ hf₀
  have h₁ := mem_vset Λ hU hf
  obtain ⟨a1, a2, a3, -, -, a4⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₁
  obtain ⟨b1, b2, b3, -⟩ :=
    TensLat.tens_selfDual_semichar_index E r X g bas idx n hs hn w hw hw1 L hL 1 _ h₀
  obtain ⟨c1, c2, c3⟩ := proj_eq idx hs hn ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ hv R hR hR'
  refine ⟨?_, c2, c3, fun Q _ c Y => ?_⟩
  · rw [c1, a4 _ h₀, ← AddSubgroup.inf_relIndex_left]
    rfl
  · rw [gphi, finsum_eq_sum_of_fintype, c2]
    refine Eq.trans ?_ Finset.smul_sum.symm
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [TensVac.heisG_smul, heisG_sum, smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [TensVac.heisG_smul, smul_smul]

end GlobalTheory.AdTh.VacProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiHalfSymplecticOrthonormalFrame
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdThSympl

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

def perL (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun u := fun j => perC X x u (idx j)
  map_add' u v := by
    funext j
    simp only [perC, Pi.add_apply]
    split_ifs
    · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    · rw [mulVec_add, Pi.add_apply]
  map_smul' c u := by
    funext j
    simp only [perC, Pi.smul_apply, RingHom.id_apply]
    split_ifs
    · simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · rw [mulVec_smul, Pi.smul_apply]

variable {X} {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)


include idx in
theorem span_emb (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range fun (v : Fin r → E) (τ : X.Ψ) => Data.emb τ.1 v) = ⊤ := by
  have h1 : (Submodule.span ℝ (Set.range fun (v : Fin r → E) (τ : X.Ψ) => Data.emb τ.1 v)).map (perL X idx x) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact span_range_pv idx hs hx
  have hsurj : Function.Surjective (perL X idx x) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← h1]
    exact LinearMap.map_le_range
  have hd : Module.finrank ℝ (X.Ψ → Fin r → ℂ) = Module.finrank ℝ (Fin g → ℂ) := by
    have := Fintype.card_congr idx
    simp only [Fintype.card_fin, Fintype.card_prod] at this
    simp only [Module.finrank_pi_fintype, finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, this]
    ring
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hsurj
  apply Submodule.map_injective_of_injective hinj
  rw [h1, Submodule.map_top, LinearMap.range_eq_top.2 hsurj]

theorem im_hx_perC (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : X.Ψ → Fin r → ℂ) :
    (GlobalTheory.Dict.hx X bas idx x (fun j => perC X x u (idx j)) (fun j => perC X x v (idx j))).im =
      ∑ τ : X.Ψ, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (u τ) (v τ)).re := by
  let B₁ : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => (Geo.Tor.hermForm (ThFr.Hm X bas idx x) (perL X idx x u) (perL X idx x v)).im)
    (fun u u' v => by simp only [Geo.Tor.hermForm, map_add (f := _), add_dotProduct, add_im])
    (fun c u v => by simp only [Geo.Tor.hermForm, map_smul, smul_dotProduct, smul_im])
    (fun u v v' => by simp only [Geo.Tor.hermForm, map_add (f := _), star_add, mulVec_add, dotProduct_add, add_im])
    (fun c u v => by simp only [Geo.Tor.hermForm, map_smul, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_im])
  let B₂ : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ
    (fun u v => ∑ τ : X.Ψ, 2 * (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (u τ) (v τ)).re)
    (fun u u' v => by simp only [hermC, Pi.add_apply, add_mul, mul_add, add_re, Finset.sum_add_distrib])
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [mul_left_comm c, ← re_ofReal_mul c, mul_left_comm (c : ℂ)]
      congr 3
      simp only [hermC, Finset.mul_sum, Pi.smul_apply, real_smul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun u v v' => by simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, add_re, Finset.sum_add_distrib])
    (fun c u v => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [mul_left_comm c, ← re_ofReal_mul c, mul_left_comm (c : ℂ)]
      congr 3
      simp only [hermC, Finset.mul_sum, Pi.smul_apply, real_smul, map_mul, conj_ofReal]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have hB : B₁ = B₂ := by
    refine LinearMap.ext_on_range (span_emb idx hs hx) fun a => LinearMap.ext_on_range (span_emb idx hs hx) fun b => ?_
    have h1 : (Geo.Tor.hermForm (ThFr.Hm X bas idx x) (pv X idx x a) (pv X idx x b)).im = (EF X a b : ℝ) :=
      im_hermForm_Hm idx hs hx a b
    refine h1.trans ?_
    rw [EF_def, TraceFormIndependence.trace_re X]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : τ.1 (herm X.Gm a b) = hermC τ.1 X.Gm (Data.emb τ.1 a) (Data.emb τ.1 b) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [herm, hermC, map_sum, map_mul, Data.emb, cc, IsCMField.complexEmbedding_complexConj]
    rw [map_mul, h2]
  rw [hx_eq_hermForm]
  exact LinearMap.congr_fun₂ hB u v

end Classical

theorem realM_tauE {D : D7} (θ : InfFam D) {m n : ℕ} (w : Mx D m n) (ρ : D.what₂.Tau) :
    realM θ w (tauE D ρ) = compAt θ ρ w := by
  have h : ∃ ρ', tauE D ρ = tauE D ρ' := ⟨ρ, rfl⟩
  rw [realM, dite_eq_left h, ← GlobalTheory.StdRat.tauE_injective D h.choose_spec]

theorem sum_four {m n : ℕ} (c : ℂ) (G : Fin m → Fin m → ℂ) (x y : Fin m → Fin n → ℂ) :
    ∑ b, 2 * (c * ∑ d, ∑ e, x d b * -G e d * conj (y e b)).re =
      -(2 * (c * ∑ a, ∑ b, ∑ e, ∑ d, (if a = b then (1 : ℂ) else 0) * conj (y e b) * G e d * x d a).re) := by
  rw [← Finset.mul_sum, ← re_sum, ← Finset.mul_sum, ← mul_neg, ← neg_re, ← mul_neg]
  congr 3
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb.symm]) (by simp), Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib, if_true]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem psi_symplOH_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x ∈ X.dom, ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV _ hM hs x hx v w hv
  subst hr
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (GlobalTheory.FockCompare.real_adele_ext_and_char D θ σ hσ _ (GlobalTheory.OrientedHeis.snd_symplO (y := w) (Or.inl hv))).2 ψ hψ
  rw [Finset.sum_congr rfl fun τ _ => GlobalTheory.OrientedHeis.valTau_symplO hθ τ v w] at e
  refine e.trans ?_
  congr 1
  rw [neg_mul, ← mul_neg, ← ofReal_neg]
  congr 2
  unfold zOf
  simp only [im_hx_perC idx hs hx]
  rw [Finset.sum_comm]
  have hb : Function.Bijective fun ρ : D.what₂.Tau => (⟨tauE D ρ, (hM.psi _).2 ⟨ρ, rfl⟩⟩ : X.Ψ) :=
    ⟨fun a b h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hM.psi τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩
  rw [← hb.sum_comp]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hk : -(X.κ0 / 2) = D.host.xi0 := by rw [hM.kap]; ring
  have hG : ∀ a b, tauE D ρ (X.Gm a b) = -tauE D ρ (W.gram b a) := fun a b => by
    rw [hM.model.1, ← map_neg]; rfl
  have h1 : ∀ a b, tauE D ρ (V.gram⁻¹ a b) = if a = b then 1 else 0 := fun a b => by
    rw [hV, inv_one, Matrix.one_apply]; split_ifs <;> simp
  simp only [realM_tauE, hk, hermC, hG, GlobalTheory.OrientedHeis.formAt, h1]
  exact (sum_four _ (fun e d => tauE D ρ (W.gram e d)) _ _).symm

theorem psi_symplOH_eq_of_isONFr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ x : Frame X.Ψ r, IsONFr X x → ∀ v w : WO V W, v.map (finPart D) = 0 → ψ (symplOH V W v w) = cexp (Real.pi * I * ((∑ b, (hx X bas idx x (zOf θ V W hr X idx x v b) (zOf θ V W hr X idx x w b)).im : ℝ) : ℂ)) :=
  fun D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x hx =>
    psi_symplOH_eq D ψ θ V W r g hr X bas idx hψ hθ hV he hM hs x (PIW.FdPA.orthonormal_domain r X x hx)

end GlobalTheory.AdThSympl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section


open GlobalTheory.UPel.HT.Hecke.PullInj in
theorem GlobalTheory.UPel.HT.Hecke.pullback_prod_injective_birigidified_galois_isogeny_alt : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ Q₁ Q₂ : LB (G2 A').left, Q₁.IsLB → Q₂.IsLB → (∃ t : (Q₁.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₁.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (Q₂.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Q₁.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) (Q₂.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → LBIso Q₁ Q₂ := by
  intro S A A' _ _ _ _ G ψ hA hA' hψ hG Q₁ Q₂ hQ₁ hQ₂ ⟨ρ₁, hρ₁⟩ ⟨σ₁, hσ₁⟩ ⟨ρ₂, hρ₂⟩ ⟨σ₂, hσ₂⟩ ⟨w, hw⟩
  have hP := _root_.GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap S A A' G ψ hψ hG
  have := hP.finite
  have := hP.fin
  have := hP.etale
  have := hP.onto
  have hT := GlobalTheory.LinDescent.locTransitive_of_isGaloisCover hP
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  let π := Hecke.sq2 ψ
  let τ : ↥G × ↥G → ((G2 A).left ⟶ (G2 A).left) :=
    fun h => (Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left
  have hτπ : ∀ c, τ c ≫ π = π := hP.inv
  have hτx : ∀ c x, π (τ c x) = π x := fun c x => congrArg (fun q : (G2 A).left ⟶ (G2 A').left => q x) (hτπ c)

  have hchart : ∀ x : (G2 A).left, ∃ k, x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := fun x => by
    obtain ⟨j₂, h₂⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j₁, h₁⟩ := exists_chart hQ₁ (π x)
    exact ⟨(fun _ => j₂, fun _ => j₁), mem_divPull.2 ⟨h₂, h₁⟩⟩

  let Inv : ↥G × ↥G → Prop := fun c => ∀ (Z : Scheme.{0}) (r : Z ⟶ (G2 A).left) (z : Z) k,
    r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ c) z _ (w.s k) = gm r z _ (w.s k)
  have hmul : ∀ a b, Inv a → Inv b → Inv (a * b) := fun a b ha hb Z r z k hk => by
    have e : r ≫ τ (a * b) = (r ≫ τ a) ≫ τ b := by rw [Category.assoc]; exact congrArg (r ≫ ·) (hP.mul a b)
    have hk' : (r ≫ τ a) z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
      have h0 := (mem_divPull (F := π)).1 hk
      refine (mem_divPull (F := π)).2 ?_
      change π (τ a (r z)) ∈ _ ∧ π (τ a (r z)) ∈ _
      rw [hτx]; exact h0
    rw [e, hb Z _ z k hk', ha Z r z k hk]

  let s₀ : (G2 A).left ⟶ A.left := (toUnit (G2 A) ≫ η[A]).left
  have hs₀ : s₀ ≫ A.hom = (G2 A).hom := by
    exact Over.w (toUnit (G2 A) ≫ η[A])

  have axis : ∀ (c : ↥G × ↥G) (e : A.left ⟶ (G2 A).left) (e' : A'.left ⟶ (G2 A').left) (T : A.left ⟶ A.left),
      e ≫ π = ψ.left ≫ e' → e ≫ (G2 A).hom = A.hom → e ≫ τ c = T ≫ e → T ≫ ψ.left = ψ.left → T ≫ A.hom = A.hom →
      (∃ ρ : LB.Gen (Q₁.pull e'), ρ.IsGen) → (∃ ρ : LB.Gen (Q₂.pull e'), ρ.IsGen) → Inv c := by
    rintro c e e' T he heS heT hTψ hTS ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩
    obtain ⟨f, hf⟩ := GlobalTheory.T.generator_translate_ratio_global_unit _ _ π Q₁ Q₂ hQ₁ hQ₂ w hw (τ c) (hτπ c)
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_axis_unit_generators_pullback _ _ _ _ ψ.left e e' π he Q₁ Q₂ hQ₁ hQ₂ w hw r₁ r₂ hr₁ hr₂
    have hTx : ∀ a, ψ.left (T a) = ψ.left a := fun a => congrArg (fun q : A.left ⟶ A'.left => q a) hTψ
    have hex : ∀ a, π (e a) = e' (ψ.left a) := fun a => congrArg (fun q : A.left ⟶ (G2 A').left => q a) he
    have hf1 : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z), gm (r ≫ e) z ⊤ f = 1 := fun Z r z => by
      obtain ⟨k, hk⟩ := hchart (e (r z))
      have hk' : e ((r ≫ T) z) ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
        have h0 := (mem_divPull (F := π)).1 hk
        refine (mem_divPull (F := π)).2 ?_
        change π (e (T (r z))) ∈ _ ∧ π (e (T (r z))) ∈ _
        rw [hex, hTx, ← hex]; exact h0
      have h1 := hf Z (r ≫ e) z k hk
      have h2 := hg Z r z k hk
      have h3 := hg Z (r ≫ T) z k hk'
      rw [Category.assoc, heT, ← Category.assoc] at h1
      rw [Category.assoc r T ψ.left, hTψ, gm_top_eq A hA g (r ≫ T) r (by rw [Category.assoc, hTS])] at h3
      rw [← h2, mul_left_inj] at h3
      rw [h3] at h1
      exact (mul_eq_right.1 h1.symm)
    intro Z r z k hk
    have hf' : gm r z ⊤ f = 1 := by
      rw [gm_top_eq (G2 A) hA2 f r (r ≫ s₀ ≫ e) (by rw [Category.assoc, Category.assoc, heS, hs₀]), ← Category.assoc]
      exact hf1 Z (r ≫ s₀) z
    rw [hf Z r z k hk, hf', _root_.one_mul]
  have inv₁ : ∀ h : ↥G, Inv (1, h) := fun h =>
    axis (1, h) (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : A' ⟶ A') (𝟙 A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_left ψ))
      (Over.w _)
      (by
        show (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (Hecke.transl (lift ((1 : ↥G) : 𝟙_ (Over S) ⟶ A) h.1)).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₁ A h.1))
      (hG.inv h) (Over.w _) ⟨ρ₁, hρ₁⟩ ⟨ρ₂, hρ₂⟩
  have inv₂ : ∀ h : ↥G, Inv (h, 1) := fun h =>
    axis (h, 1) (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 A') (1 : A' ⟶ A')).left (Hecke.transl h.1).left
      (congrArg (·.left) (grpScheme_monHom_square_lift_one_right ψ))
      (Over.w _)
      (by
        show (lift (𝟙 A) (1 : A ⟶ A)).left ≫ (Hecke.transl (lift h.1 ((1 : ↥G) : 𝟙_ (Over S) ⟶ A))).left = _
        rw [OneMemClass.coe_one, ← Over.comp_left, ← Over.comp_left]
        exact congrArg (·.left) (transl_axis₂ A h.1))
      (hG.inv h) (Over.w _) ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩
  have inv : ∀ c, Inv c := fun c => by
    have e : c = (c.1, 1) * (1, c.2) := Prod.ext (_root_.mul_one c.1).symm (_root_.one_mul c.2).symm
    rw [e]
    exact hmul _ _ (inv₂ c.1) (inv₁ c.2)

  have hdesc : ∀ p : Q₂.ι × Q₁.ι, ∃ g : Γ((G2 A').left, Q₂.U p.1 ⊓ Q₁.U p.2)ˣ, ∀ (Z : Scheme.{0})
      (r : Z ⟶ (G2 A).left) (z : Z), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) →
      gm (r ≫ π) z _ g = gm r z _ (w.s (fun _ => p.1, fun _ => p.2)) := fun p => by
    obtain ⟨g, hg⟩ := GlobalTheory.LinDescent.LocTransitive.exists_descend_unit hT (Q₂.U p.1 ⊓ Q₁.U p.2)
      (κ := Unit) (fun _ => (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2))
      (fun _ x hx => (mem_divPull (F := π)).1 hx)
      (fun x hx => ⟨(), (mem_divPull (F := π)).2 hx⟩)
      (fun _ => w.s (fun _ => p.1, fun _ => p.2)) (fun _ _ _ _ _ => rfl)
      (fun c Z r z hz => by
        have hz' : r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
          (mem_divPull (F := π)).2 hz
        refine ⟨(), (), hz', ?_, inv c Z r z _ hz'⟩
        refine (mem_divPull (F := π)).2 ?_
        change π (τ c (r z)) ∈ _ ∧ π (τ c (r z)) ∈ _
        rw [hτx]; exact hz)
    exact ⟨g, fun Z r z hz => hg Z r z () hz⟩
  choose g hg using hdesc
  refine ⟨⟨g⟩, fun p q => ?_⟩
  apply GlobalTheory.LinDescent.unit_ext_of_flat (π := π)
  intro x hx
  have hp : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => p.1, fun _ => p.2) :=
    (mem_divPull (F := π)).2 hx.1
  have hq : x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => q.1, fun _ => q.2) :=
    (mem_divPull (F := π)).2 hx.2
  have e1 := gen_germ hw (𝟙 _) x hp hq
  rw [germ_div_g _ _ (𝟙 _) x hp hq, gm_pull_g Q₂ π (𝟙 _) x hx.1.1 hx.2.1,
    gm_pull_g Q₁ π (𝟙 _) x hx.1.2 hx.2.2] at e1
  refine ((gm_res (𝟙 _ ≫ π) x inf_le_left hx (g p)).trans (hg p _ (𝟙 _) x hp)).trans ?_
  rw [e1, map_mul, gm_res (𝟙 _ ≫ π) x inf_le_right hx (g q), germ_div_g Q₂ Q₁ (𝟙 _ ≫ π) x hx.1 hx.2]
  exact congrArg (_ * ·) (hg q _ (𝟙 _) x hq).symm
end
end

