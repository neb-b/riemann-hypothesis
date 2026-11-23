module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionLinearInSectionStatement
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsIntegralCoeffCof
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

noncomputable section

namespace GlobalTheory.FrameRead.CoefMap

def harmSub {T : Type} (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Submodule k (MvPolynomial (Letter T r n) k) where
  carrier := HHa r n k cc isX a
  add_mem' := by
    rintro P Q ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨add_mem h1 h1', fun σ i i' h t => by rw [map_add (f := _), h2 σ i i' h t, h2' σ i i' h t], fun m hm => ?_⟩
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact h3 m h
    · exact h3' m h
  zero_mem' := ⟨zero_mem _, fun σ i i' _ t => map_zero _, fun m hm => by simp at hm⟩
  smul_mem' := by
    rintro x P ⟨h1, h2, h3⟩
    exact ⟨Submodule.smul_mem _ x h1, fun σ i i' h t => by rw [map_smul, h2 σ i i' h t],
      fun m hm => h3 m (support_smul hm)⟩

theorem det_gen_ne_zero (K : Type) [Field K] {Ix : Type} (n : ℕ) (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (eval (fun v : Ix × Fin n × Fin n => if v.2.1 = v.2.2 then (1 : K) else 0)).mapMatrix (gen K n t) = 1 := by
    ext p q
    simp [gen, Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem map_gen {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {Ix : Type} (n : ℕ) (t : Ix) :
    (MvPolynomial.map f).mapMatrix (gen R n t) = gen S n t := by
  ext p q : 2
  simp [gen]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {n : ℕ}
  {Ix : Type} [Fintype Ix] (pl : Ix → (E →+* ℂ))

theorem detFac_ne_zero (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n) :
    detFac Dw pl K a s lam ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun t _ => pow_ne_zero _ (det_gen_ne_zero K n t)

theorem map_cof {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Q : MvPolynomial (LtN Dw n) R) :
    MvPolynomial.map f (cof Dw pl R n Q) = cof Dw pl S n (MvPolynomial.map f Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp [algHom_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p ℓ hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cof, aeval_X]
    split_ifs with h1 h2 h3
    · simp [gen]
    · rw [← map_gen f, ← RingHom.map_adjugate]
      rfl
    · simp
    · simp

theorem isIntegral_coeff_cof {K : Type} [Field K] (P : MvPolynomial (LtN Dw n) K)
    (hP : ∀ m, P.coeff m ∈ (integralClosure ℤ K).toSubring) (m) : IsIntegral ℤ ((cof Dw pl K n P).coeff m) := by
  obtain ⟨Q, rfl⟩ : ∃ Q, MvPolynomial.map (integralClosure ℤ K).toSubring.subtype Q = P := by
    refine ⟨∑ m ∈ P.support, monomial m ⟨P.coeff m, hP m⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_monomial, Subring.subtype_apply]
    exact P.as_sum.symm
  rw [← map_cof, coeff_map]
  exact ((cof Dw pl _ n Q).coeff m).2


set_option maxHeartbeats 1000000 in
theorem exists_ioLFRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ (io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (hw : VVc c lam), IoLFRec c (fun t => embF c (pl t)) lam a io hw := by
  intro E _ _ _ H Dw n Ix _ pl he hn l c a s lam ha hwt
  obtain ⟨ε, hε⟩ := GlobalTheory.T.frameReading_leadingMinorProduct_extremal E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨him, hex, heq⟩ := _root_.GlobalTheory.FrameRead.cof_image E H Dw n Ix pl he hn l c a s lam ha hwt
  obtain ⟨hpG, -, -⟩ := pG_mem_ne_zero_generates E H Dw n Ix pl he hn l c a ha
  obtain ⟨-, -, hstab⟩ := letAct_mul_one_mem_HHa E H Dw n Ix pl he hn c.F a
  obtain ⟨hs1, hs2, hs3⟩ := GlobalTheory.StdNab.nabAtr_stdLat E c.F Ix n (fun t => embF c (pl t)) lam
  have hD := detFac_ne_zero Dw pl c.F a s lam
  let S := harmSub Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
  have hS : ∀ P, P ∈ S ↔ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) :=
    fun _ => Iff.rfl
  set e : c.F := ((ε : ℤ) : c.F) with he'
  have hee : e * e = 1 := by
    rw [he', ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have heI : IsIntegral ℤ e := isIntegral_intCast _
  set D := detFac Dw pl c.F a s lam with hDdef
  have hex' : ∀ F : VVc c lam, ∃! P, P ∈ S ∧ cof Dw pl c.F n P = e • (D * F.1) := fun F => by
    have := hex (e • F.1) (Submodule.smul_mem _ _ F.2)
    rwa [mul_smul_comm] at this
  choose φ hφ huniq using hex'
  have hu : ∀ (F : VVc c lam) P, P ∈ S → cof Dw pl c.F n P = e • (D * F.1) → φ F = P :=
    fun F P h1 h2 => (huniq F P ⟨h1, h2⟩).symm
  let io : VVc c lam →ₗ[c.F] MvPolynomial (LtN Dw n) c.F :=
    { toFun := φ
      map_add' := fun F G => hu _ _ (add_mem (hφ F).1 (hφ G).1) (by
        rw [map_add (f := _), (hφ F).2, (hφ G).2, Submodule.coe_add, mul_add, smul_add])
      map_smul' := fun x F => hu _ _ (Submodule.smul_mem _ _ (hφ F).1) (by
        rw [map_smul, (hφ F).2, Submodule.coe_smul, mul_smul_comm, smul_comm]; rfl) }
  have hio : ∀ F, io F = φ F := fun _ => rfl
  have hsurj : ∀ P ∈ S, ∃ F : VVc c lam, io F = P := fun P hP => by
    obtain ⟨F, hF, h⟩ := him P hP
    refine ⟨⟨e • F, Submodule.smul_mem _ _ hF⟩, hu _ _ hP ?_⟩
    rw [h, mul_smul_comm, smul_smul, hee, one_smul]
  have hwm : (ten fun t => extremal c.F n (lam t)) ∈ VV c.F lam := by
    obtain ⟨F, hF, h⟩ := him _ hpG.1
    rw [hε, ← mul_smul_comm] at h
    have h' := mul_left_cancel₀ hD h
    have : (ten fun t => extremal c.F n (lam t)) = e • F := by rw [← h', smul_smul, hee, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hF
  refine ⟨io, ⟨_, hwm⟩, rfl, fun ga => if h : IsUnit ga.det then
      ∏ t, (((invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h))) t : GL (Fin n) c.F) :
        Matrix (Fin n) (Fin n) c.F).det ^ (s t) else 0, hn, ?_, ?_, ?_, (hs1 _).2 hs2,
      fun x hx => hs3 x ((hs1 _).1 hx), hu _ _ hpG.1 hε, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro F hF
    have h := (hφ F).2
    rw [← hio, hF, map_zero] at h
    have h' := congrArg (fun x => e • x) h
    simp only [smul_zero, smul_smul, hee, one_smul] at h'
    exact Subtype.ext ((mul_eq_zero.1 h'.symm).resolve_left hD)
  · have : Submodule.span c.F (HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) = S :=
      Submodule.span_eq S
    rw [this]
    refine le_antisymm ?_ hsurj
    rintro _ ⟨F, rfl⟩
    exact (hφ F).1
  · intro ga hga F
    have h : IsUnit ga.det := by
      have := congrArg Matrix.det hga
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one_right _ this
    rw [gaStar_conj_eq_letAct E H Dw n Ix pl he hn l c ga h hga]
    simp only [dif_pos h, rhoM]
    set g := invTrK (embGL (fun t => embF c (pl t)) (Matrix.nonsingInvUnit ga h)) with hg
    refine hu _ _ (Submodule.smul_mem _ _ (hstab g _ (hφ F).1)) ?_
    have h1 := heq g _ (hφ F).1 (e • F.1) (Submodule.smul_mem _ _ F.2) (by rw [(hφ F).2, mul_smul_comm])
    rw [map_smul, hio, h1, smul_smul, ← Finset.prod_mul_distrib, map_smul, mul_smul_comm]
    have h2 : ∏ t, (g t : Matrix (Fin n) (Fin n) c.F).det ^ (s t) * (g t : Matrix (Fin n) (Fin n) c.F).det ^ (-(s t)) = 1 :=
      Finset.prod_eq_one fun t _ => by
        rw [← zpow_add₀ (Matrix.isUnits_det_units (g t)).ne_zero, add_neg_cancel, zpow_zero]
    rw [h2, one_smul]
    rfl
  · intro P hP
    obtain ⟨F, rfl⟩ := hsurj P hP.1
    refine ⟨F, (hs1 F).2 (GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral c.F Ix n lam
      (fun t => ((degC Dw pl a t : ℤ) + (lam t).detShift - s t).toNat) F.1 F.2 fun m => ?_), rfl⟩
    have h : e • cof Dw pl c.F n (φ F) = D * F.1 := by rw [(hφ F).2, smul_smul, hee, one_smul]
    change IsIntegral ℤ ((D * F.1).coeff m)
    rw [← h, coeff_smul, smul_eq_mul]
    exact heI.mul (isIntegral_coeff_cof Dw pl (φ F) hP.2 m)

end GlobalTheory.FrameRead.CoefMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRepsLevelTranslates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ}

theorem levReps_act_mul (a b : 𝓞 E) (v : I2.Vsp dim) : I2.act a (I2.act b v) = I2.act (a * b) v := by
  ext i
  simp only [I2.act, RingOfIntegers.coe_eq_algebraMap, map_mul]
  exact (mul_assoc _ _ _).symm

theorem levReps_act_nat (m : ℕ) (v : I2.Vsp dim) : I2.act (m : 𝓞 E) v = (m : ℂ) • v := by
  ext i
  simp [I2.act]

theorem levReps_act_smul (a : 𝓞 E) (c : ℂ) (v : I2.Vsp dim) : I2.act a (c • v) = c • I2.act a v := by
  ext i
  simp [I2.act]
  ring

theorem levReps_act_add (a : 𝓞 E) (v w : I2.Vsp dim) : I2.act a (v + w) = I2.act a v + I2.act a w := by
  ext i
  simp [I2.act, mul_add]

theorem levReps_act_neg (a : 𝓞 E) (v : I2.Vsp dim) : I2.act a (-v) = -I2.act a v := by
  ext i
  simp [I2.act]

end

theorem isReps_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (T : I2.PT E) (mk : Dw.La →+ I2.Vsp T.dim) (α : 𝓞 E), α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → (∀ a, mk a ∈ T.L) → (∀ (β : 𝓞 E) a, mk (β • a) = I2.act β (mk a)) → (∀ a, (∃ v ∈ T.L, mk a = (l.M : ℂ) • v) → ∃ b, a = l.M • b) → (∀ v ∈ T.L, ∃ a, ∃ v' ∈ T.L, v = mk a + (l.M : ℂ) • v') → ∀ x2 : LevQ Dw l → Dw.La, (∀ q, x2 q ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ q, x2 q - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ n : ℕ, ∃ K : Finset (Fin n → I2.Vsp T.dim), I2.IsReps T l.M n (vspActL α) K ∧ ∀ b ∈ K, ∃ q : Fin n → LevQ Dw l, b = fun i => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 (q i)))) := by
  intro E _ _ _ H Dw l T mk α hα hMb hL hlin hinj hsurj x2 hx2 hrep n
  classical
  haveI : Finite (LevQ Dw l) := (card_levQ E H Dw l).1
  haveI : Fintype (LevQ Dw l) := Fintype.ofFinite _
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hbb : H.bar (H.bar α) = α := by
    apply Subtype.ext
    change ((H.bar (H.bar α) : 𝓞 E) : E) = (α : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hmap : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {α} := by
    rw [hMb, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) hbb
  have hsm : ∀ (c : 𝓞 E) (y : Dw.La), y ∈ Ideal.span {c} • (⊤ : Submodule (𝓞 E) Dw.La) ↔ ∃ z, y = c • z := by
    intro c y
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨z, _, h⟩ => ⟨z, h.symm⟩, fun ⟨z, h⟩ => ⟨z, trivial, h.symm⟩⟩
  have hu : ∀ q, ∃ u : Dw.La, x2 q = α • α • u := by
    intro q
    have h := hx2 q
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hsm] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨(2 : 𝓞 E) • z, ?_⟩
    rw [hz, smul_smul, smul_smul]
    congr 1
    ring
  have hcls : ∀ q, (Submodule.Quotient.mk (x2 q) : LevQ Dw l) = q := by
    intro q
    rw [(Submodule.Quotient.eq _).2 (hrep q)]
    exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  obtain ⟨r, s, hrs⟩ : ∃ r s : 𝓞 E, r * H.bar α + s * α = 1 := by
    have h := l.coprime
    rw [hmap, hMb, Ideal.eq_top_iff_one, ← Ideal.span_insert, Ideal.mem_span_pair] at h
    exact h
  set t : LevQ Dw l → I2.Vsp T.dim := fun q => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 q))) with ht
  have hαt : ∀ q, I2.act α (t q) = -((l.M : ℂ)⁻¹ • mk (x2 q)) := by
    intro q
    simp only [ht]
    rw [levReps_act_mul, hα, levReps_act_nat, smul_neg, smul_smul]
    congr 2
    field_simp
  have hMt : ∀ q, (l.M : ℂ) • t q ∈ T.L := by
    intro q
    obtain ⟨u, hq⟩ := hu q
    have : (l.M : ℂ) • t q = -mk (α • u) := by
      simp only [ht]
      rw [hq, hlin α (α • u), levReps_act_neg, levReps_act_smul, levReps_act_mul, mul_comm (H.bar α), hα,
        levReps_act_nat, smul_neg, smul_smul, smul_smul]
      have : (l.M : ℂ) * ((l.M : ℂ) ^ 2)⁻¹ * l.M = 1 := by field_simp
      rw [this, one_smul]
    rw [this]
    exact T.L.neg_mem (hL _)
  have hsub : ∀ (b : I2.Vsp T.dim) q, vspActL α (b - t q) = I2.act α b + (l.M : ℂ)⁻¹ • mk (x2 q) := by
    intro b q
    rw [map_sub]
    change I2.act α b - I2.act α (t q) = _
    rw [hαt, sub_neg_eq_add]
  have hex : ∀ b : I2.Vsp T.dim, (l.M : ℂ) • b ∈ T.L → ∃ q, vspActL α (b - t q) ∈ T.L := by
    intro b hb
    obtain ⟨a, v', hv', hab⟩ := hsurj _ hb
    refine ⟨Submodule.Quotient.mk (-(α • a)), ?_⟩
    set q : LevQ Dw l := Submodule.Quotient.mk (-(α • a)) with hq
    have h1 : x2 q - -(α • a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 ((hcls q).trans hq)
    rw [hMb, hsm] at h1
    obtain ⟨d, hd⟩ := h1
    obtain ⟨u, hqu⟩ := hu q
    have h2 : x2 q + α • a = (l.M : 𝓞 E) • (r • (α • u + a) + s • d) := by
      have e1 : x2 q + α • a = α • (α • u + a) := by rw [hqu, smul_add]
      have e2 : x2 q + α • a = H.bar α • d := by rw [← hd, sub_neg_eq_add]
      calc x2 q + α • a = (r * H.bar α + s * α) • (x2 q + α • a) := by rw [hrs, one_smul]
        _ = (r * H.bar α) • α • (α • u + a) + (s * α) • H.bar α • d := by rw [add_smul, ← e1, ← e2]
        _ = _ := by
          rw [← hα, smul_add (α * H.bar α)]
          simp only [smul_smul (r * H.bar α), smul_smul (s * α), smul_smul (α * H.bar α)]
          congr 2 <;> ring
    have hb' : b = (l.M : ℂ)⁻¹ • mk a + v' := by
      calc b = (l.M : ℂ)⁻¹ • (l.M : ℂ) • b := by rw [smul_smul, inv_mul_cancel₀ hM, one_smul]
        _ = _ := by rw [hab, smul_add, smul_smul, inv_mul_cancel₀ hM, one_smul]
    have h3 : vspActL α (b - t q) = mk (r • (α • u + a) + s • d) + I2.act α v' := by
      rw [hsub, hb', levReps_act_add, levReps_act_smul, ← hlin, add_right_comm, ← smul_add, ← map_add (f := _),
        add_comm (α • a), h2, hlin, levReps_act_nat, smul_smul, inv_mul_cancel₀ hM, one_smul]
    rw [h3]
    exact T.L.add_mem (hL _) (T.stable _ _ hv')
  have huniq : ∀ (b : I2.Vsp T.dim) q q', vspActL α (b - t q) ∈ T.L → vspActL α (b - t q') ∈ T.L → q = q' := by
    intro b q q' h h'
    have h1 := T.L.sub_mem h h'
    rw [hsub, hsub, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub] at h1
    obtain ⟨z, hz⟩ := hinj (x2 q - x2 q') ⟨_, h1, by rw [smul_smul, mul_inv_cancel₀ hM, one_smul]⟩
    rw [← hcls q, ← hcls q']
    refine (Submodule.Quotient.eq _).2 ?_
    rw [hMb, hsm]
    exact ⟨α • z, by rw [hz, smul_smul, mul_comm, hα, Nat.cast_smul_eq_nsmul]⟩
  refine ⟨Finset.univ.image (fun q : Fin n → LevQ Dw l => fun i => t (q i)), ⟨?_, ?_⟩, ?_⟩
  · intro b hb k
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact hMt _
  · intro b hb
    choose q hq using fun k => hex (b k) (hb k)
    refine ⟨fun i => t (q i), ⟨Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hq⟩, ?_⟩
    rintro b' ⟨hb', h'⟩
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb'
    funext k
    rw [huniq (b k) _ _ (h' k) (hq k)]
  · intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨q, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem shortSum_toΓ_injective (S : Type) [CommRing S] : Function.Injective (toΓ S) := by
  intro a b h
  have hinv : ∀ x : S, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (toΓ S x) = x := by
    intro x
    unfold toΓ
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hinv a, ← hinv b, h]

private theorem eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one {M : Type*} [CommMonoid M] (x : M) (N : ℕ) (hN : Odd N)
    (h2 : x ^ 2 = 1) (hN2 : x ^ (N ^ 2) = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hN.pow (n := 2)
  rw [hk, pow_succ, pow_mul, h2, one_pow, _root_.one_mul] at hN2
  exact hN2


set_option maxHeartbeats 1000000 in
theorem shortSum_indep_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  intro hL E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hTr hLev P T _ _ _ y z1 tp1 F1 z2 tp2 F2 hz1 hg1 htp1 hF1 hz2 hg2 htp2 hF2 q
  obtain ⟨hNodd, hMN, hNL⟩ := hLev
  have hN0 : 0 < N := hNodd.pos
  have hLa : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La := hNL.trans inf_le_left
  have hsurj := (_root_.GlobalTheory.isotropic_enumeration_onto_of_isLocalRing hL E H Dw l Xo T y.x n Λ N hU hN0 hLa z1 hz1 hg1).1
  have h58 := _root_.GlobalTheory.zh_isotropic_and_half_isotropic hL E H Dw l Xo T y.x n Λ N hU hN0 hLa
  have h56 := _root_.GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  have h57 := (GlobalTheory.UnivPairing.weilIs_univ_pull_exists_unique hL E H Dw l Xo N hN0).2.1

  have hz2inj : Function.Injective z2 := by
    intro i i' h
    let g : ptO Xo (spMap (IsLocalRing.residue T) ≫ y.x) ⟶ ptO Xo y.x :=
      Over.homMk (spMap (IsLocalRing.residue T)) rfl
    exact hg2 (IsLocalRing.ResidueField T) (IsLocalRing.residue T) g rfl
      (congrArg (fun (w : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (b : Fin n) => g ≫ w b) h)

  obtain ⟨u, hu⟩ : ∃ u : Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G), ∀ b, u b = (tp1 q b)⁻¹ * tp2 q b :=
    ⟨_, fun _ => rfl⟩
  have htp : ∀ b, tp2 q b = tp1 q b * u b := fun b => by
    rw [hu, mul_inv_cancel_left]
  have hlev : ∀ a : Dw.La, levPt Xo y.x a ^ N = 1 := by
    intro a
    obtain ⟨k, hk⟩ := hMN
    unfold levPt
    rw [← MonObj.comp_pow, hk, pow_mul, (GlobalTheory.moduli_univ_eta_killed hL E H Dw l Xo a).2.2, one_pow,
      MonObj.comp_one]
  have hu1 : ∀ b, u b ^ N = 1 := fun b => by
    rw [hu, mul_pow, inv_pow, (htp1 q b).1, (htp2 q b).1, inv_mul_cancel]
  have hsq : ∀ x : ptO Xo y.x ⟶ Xo.univ.t.G, x ^ N = 1 → x ^ (N ^ 2) = 1 := fun x hx => by
    rw [sq, pow_mul, hx, one_pow]
  have ht2 : ∀ b, tp1 q b ^ (N ^ 2) = 1 := fun b => by
    rw [sq, pow_mul, (htp1 q b).1, hlev]
  have hkill : ∀ b, ∃ j, KilledBy Xo (l.Mb ^ j) (tp1 q b) ∧ KilledBy Xo (l.Mb ^ j) (u b) := by
    intro b
    obtain ⟨j1, hj1⟩ := (htp1 q b).2
    obtain ⟨j2, hj2⟩ := (htp2 q b).2
    have mono : ∀ {i j : ℕ} (t : ptO Xo y.x ⟶ Xo.univ.t.G), i ≤ j →
        KilledBy Xo (l.Mb ^ i) t → KilledBy Xo (l.Mb ^ j) t :=
      fun t hij ht a ha => ht a (Ideal.pow_le_pow_right hij ha)
    refine ⟨max j1 j2, mono _ (le_max_left _ _) hj1, ?_⟩
    intro a ha
    have := Xo.univ.t.act.hom a
    have k1 := mono _ (le_max_left _ _) hj1 a ha
    have k2 := mono _ (le_max_right _ _) hj2 a ha
    have h1 : ((tp1 q b)⁻¹ ≫ Xo.univ.t.act.act a) * (tp1 q b ≫ Xo.univ.t.act.act a) = 1 := by
      rw [← MonObj.mul_comp, inv_mul_cancel, MonObj.one_comp]
    rw [k1, _root_.mul_one] at h1
    rw [hu, MonObj.mul_comp, h1, k2, _root_.one_mul]
  have hInU : InZh Xo Λ N u := h56.2.2.2 hTr (ptO Xo y.x) u (fun b => by
    obtain ⟨j, -, hj⟩ := hkill b
    exact ⟨hu1 b, j, hj⟩)

  have hw : ∀ i, ∃ j, z1 j = fun b => u b * z2 i b := fun i =>
    hsurj _ (h56.2.1 _ u (z2 i) hInU (hz2 i))
  choose ρ hρ using hw
  have hρinj : Function.Injective ρ := by
    intro i i' h
    apply hz2inj
    funext b
    have hii := (hρ i).symm.trans ((congrArg z1 h).trans (hρ i'))
    exact mul_left_cancel (show u b * z2 i b = u b * z2 i' b from congrFun hii b)
  have hρbij : Function.Bijective ρ := Finite.injective_iff_bijective.mp hρinj

  have key : ∀ i, (∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
        ∏ b, nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) (colOf m b) := by
    intro i
    have he : ∀ b, ∃ e : Γ((ptO Xo y.x).left, ⊤)ˣ,
        WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (u b) (z2 i b) e := fun b =>
      (h57 (ptO Xo y.x) (u b) (z2 i b) (hsq _ (hu1 b)) ((hz2 i).1 b)).imp fun _ h => h.1
    choose e he using he
    have hpe : ∏ b, e b = 1 := h58.1 u (z2 i) e hInU (hz2 i) he
    have hr : ∀ b, ∃ r : T, (toΓ T r) ^ 2 = ((e b : Γ((ptO Xo y.x).left, ⊤))) ∧ r ^ (N ^ 2) = 1 ∧
        ∀ α, nab y ((N : ℤ) ^ 2) (F2 q i b) α = r * nab y ((N : ℤ) ^ 2) (F1 q (ρ i) b) α := by
      intro b
      obtain ⟨j, hj1, hj2⟩ := hkill b
      have hW1 := h58.2 (tp1 q b) (u b) j (ht2 b) (hsq _ (hu1 b)) hj1 hj2
      have hA : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp1 q b * u b) (F2 q i b) := by
        rw [← htp b]
        exact hF2 q i b
      have hB : IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (u b * z2 i b) (tp1 q b) (F1 q (ρ i) b) := by
        have h1 := hF1 q (ρ i) b
        rw [hρ i] at h1
        exact h1
      obtain ⟨r, hr1, hr2, hr3⟩ := GlobalTheory.T.thetaGroup_shift_halfTorsion_root hL E H Dw l Xo T y.x N hNodd y.s (tp1 q b) (u b) (z2 i b)
        (e b) (ht2 b) (hsq _ (hu1 b)) ((hz2 i).1 b) hW1 (he b) _ _ hA hB
      exact ⟨r, hr1, hr2, GlobalTheory.T.connection_linear_in_section E H Dw l Xo c nab hnab T y N _ _ r hr3⟩
    choose r hr using hr
    have hprod : ∏ b, r b = 1 := by
      apply eq_one_of_sq_eq_one_of_pow_odd_sq_eq_one _ N hNodd
      · apply shortSum_toΓ_injective T
        rw [map_one, map_pow, map_prod, ← Finset.prod_pow,
          Finset.prod_congr rfl (fun b _ => (hr b).1), ← Units.coe_prod, hpe, Units.val_one]
      · rw [← Finset.prod_pow]
        exact Finset.prod_eq_one (fun b _ => (hr b).2.1)
    refine Finset.sum_congr rfl (fun m _ => ?_)
    congr 1
    rw [Finset.prod_congr rfl (fun b _ => (hr b).2.2 (colOf m b)), Finset.prod_mul_distrib, hprod, _root_.one_mul]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  exact (hρbij.sum_comp (fun j => ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
    ∏ b, nab y ((N : ℤ) ^ 2) (F1 q j b) (colOf m b))).symm

end GlobalTheory
end

