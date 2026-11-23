module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.StatementU
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant
public import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsLawOfOfMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LinkLaw

variable {V : Type} [CommRing V]

theorem jetMap_coord {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (j : κ) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = Ideal.Quotient.mk _ (φ j) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X j)) = _
  rw [MvPolynomial.aeval_X]

theorem jetSubstP_coord {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (F : κ → MvPowerSeries κ' V) (j : κ)
    (h : MvPowerSeries.constantCoeff (F j) = 0) :
    jetSubstP m (fun p => psTrunc m (F p)) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (F j) := by
  unfold jetSubstP
  rw [jetMap_coord]
  have h0 : MvPolynomial.constantCoeff (psTrunc m (F j)) = 0 := by
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq,
      MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  rw [h0, map_zero, sub_zero]
  exact congrArg (Ideal.Quotient.mk _) (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq m (F j))

def toAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by dsimp; simp)

theorem read_match {G : Over (Sp V)} {κ : Type} {N m : ℕ} (z : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (x : Chart.sp (R₀ := V) (Chart.JetR V (Fin N) m) ⟶ G) (e : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m)
    (he : z.left = Geo.Tor.spMap (e : Chart.JetR V (Fin N) m →+* Jet V κ m) ≫ x.left)
    {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (S : Jet V κ m →ₐ[V] B) (Φ : B →ₐ[V] A) :
    (toAt A ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) Φ) ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) S ≫ z =
      Chart.spMap (Φ.comp (S.comp (e : Chart.JetR V (Fin N) m →ₐ[V] Jet V κ m))) ≫ x := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, he, Chart.spMap_left, toAt, Formalism.L2.Pj.homAt, Over.homMk_left, Category.id_comp,
    ← Category.assoc]
  congr 1
  simp only [Geo.Tor.spMap, ← Spec.map_comp]
  rfl

theorem constantCoeff_ev {k n d : ℕ} (a : Fin k → Pt V n d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (f : PS V k d) (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 := by
  unfold ev
  have h1 : ∀ p : Fin k × Fin d, MvPowerSeries.constantCoeff ((fun p : Fin k × Fin d => a p.1 p.2) p) = 0 :=
    fun p => ha p.1 p.2
  have h2 : MvPowerSeries.HasSubst (fun p : Fin k × Fin d => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero h1
  exact MvPowerSeries.constantCoeff_subst_eq_zero (a := fun p : Fin k × Fin d => a p.1 p.2) h2 h1 hf

theorem exists_subst {σ κ : Type} [Finite σ] [Finite κ] (c : σ → MvPowerSeries κ V)
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) (m : ℕ) :
    ∃ Φ : Jet V σ m →ₐ[V] Chart.JetR V κ m,
      (∀ j, Φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (c j)) ∧
      ∀ g : MvPowerSeries σ V, Φ (JetSer.toJet m g) = JetSer.toJet m (MvPowerSeries.subst c g) := by
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg V κ).2.2.2.2 σ c hc m
  exact ⟨Φ, hΦ, hsub Φ hΦ⟩

theorem isLawOf_of_match {G : Over (Sp V)} [GrpObj G] {d : ℕ} (F : Fin d → PS V 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) (xT : JetPts G (Fin 1 × Fin d))
    (law : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ xT m =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ xT m) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ xT m))
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsLawOf x F := by
  refine ⟨hF, fun n a b y z hy hz => ?_⟩
  have hab : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact hy.1 j
    · exact hz.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hF j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨ψb, hb1, hb2⟩ := hz.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ i : Fin 2, ∀ j, (Φ.comp ((jetCopy d m i).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) =
      JetSer.toJet m ((![a, b] : Fin 2 → Pt V n d) i j) := by
    intro i j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, jetCopy, jetMap_coord]
    exact hΦ (i, j)
  have ea : ψa = Φ.comp ((jetCopy d m 0).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key 0 j).symm
  have eb : ψb = Φ.comp ((jetCopy d m 1).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (hb1 j).trans (key 1 j).symm
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => F p.2) _ (hF _)]
    exact hsub _
  · show y m * z m = _
    rw [← read_match (xT m) (x m) e he2, law m, MonObj.comp_mul,
      read_match (xT m) (x m) e he2, read_match (xT m) (x m) e he2, ← ea, ← eb, ← ha2, ← hb2]

theorem isMapOf_of_match {G : Over (Sp V)} {d : ℕ} (φ : Pt V 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (xT : JetPts G (Fin 1 × Fin d)) (f : G ⟶ G)
    (hf : ∀ m, xT m ≫ f =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)) ≫ xT m)
    (x : JetSer.Fam G (Fin d)) (hM : Match (oneCol d) xT x) : JetSer.IsMapOf x x f φ := by
  refine ⟨hφ, fun n a y hy => ?_⟩
  have hab : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt V n d) i j) = 0 := by
    intro i j
    fin_cases i
    exact hy.1 j
  refine ⟨fun j => constantCoeff_ev _ hab _ (hφ j), fun m => ?_⟩
  obtain ⟨e, he1, he2⟩ := hM m
  obtain ⟨ψa, ha1, ha2⟩ := hy.2 m
  obtain ⟨Φ, hΦ, hsub⟩ := exists_subst
    (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Pt V n d) p.1 p.2) (fun p => hab p.1 p.2) m
  have key : ∀ j, (Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m))) (Chart.zR m j) = JetSer.toJet m (a j) := by
    intro j
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1, AlgHom.id_apply]
    exact hΦ (0, j)
  have ea : ψa = Φ.comp ((AlgHom.id V _).comp
      (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)) :=
    Chart.jet_ext fun j => (ha1 j).trans (key j).symm
  have hid : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (AlgHom.id V (Jet V (Fin 1 × Fin d) m)) = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  refine ⟨Φ.comp ((jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (φ p.2)).comp
    (e : Chart.JetR V (Fin d) m →ₐ[V] Jet V (Fin 1 × Fin d) m)), fun j => ?_, ?_⟩
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom, he1,
      jetSubstP_coord m (fun p : Fin 1 × Fin d => φ p.2) _ (hφ _)]
    exact hsub _
  · show y m ≫ f = _
    rw [← read_match (xT m) (x m) e he2, ← hf m, ha2, ea, ← read_match (xT m) (x m) e he2, hid,
      Category.id_comp]
    simp only [Category.assoc]

theorem linkLaw : LinkLawSt := by
  intro E _ _ _ H V _ t d BT tg xT eT wPT hC _ _ x _ hM
  letI := H.starRing
  exact ⟨isLawOf_of_match BT.G.F BT.G.const xT hC.law x hM,
    fun α => isMapOf_of_match (BT.A.act α) (BT.A.const α) xT _ (fun m => hC.act m α) x hM⟩

end GlobalTheory.LinkLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPolyDegStar
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgContr

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

private lemma star_eval_eq_eval₂_starRingEnd {σ : Type*} (x : σ → ℂ) (q : MvPolynomial σ ℂ) :
    star (MvPolynomial.eval x q) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun v => star (x v)) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p v hp => simp [hp]

theorem isPolyDeg_star {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (le_trans (by
        unfold MvPolynomial.totalDegree
        exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)) hq)
  · intro g
    show star (P g) = _
    rw [hP g, MvPolynomial.eval_rename, MvPolynomial.eval_map, star_eval_eq_eval₂_starRingEnd]
    congr 1
    funext v
    cases v <;> simp

theorem isPolyDeg_pow {a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (n : ℕ) :
    U.IsPolyDeg (n * a) (fun g => P g ^ n) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨q ^ n, (MvPolynomial.totalDegree_pow q n).trans (Nat.mul_le_mul_left n hq), ?_⟩
  intro g
  simp [hP g]

theorem isPolyDeg_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i, U.IsPolyDeg (d i) (P i)) : U.IsPolyDeg (∑ i ∈ s, d i) (fun g => ∏ i ∈ s, P i g) := by
  choose q hq hP using h
  refine ⟨∏ i ∈ s, q i, (MvPolynomial.totalDegree_finsetProd s q).trans (Finset.sum_le_sum fun i _ => hq i), ?_⟩
  intro g
  simp [hP]

private lemma isPolyDeg_const (c : ℂ) (a : ℕ) : U.IsPolyDeg (N := N) a (fun _ => c) :=
  ⟨MvPolynomial.C c, by simp, fun g => by simp⟩

private lemma exists_pow_mul_mul_mem_subring {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P)
    (hQ : U.IsPolyDeg b Q) : U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hPe⟩ := hP
  obtain ⟨q, hq, hQe⟩ := hQ
  exact ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => by simp [hPe, hQe]⟩

private lemma exists_pow_mul_finset_sum_mem_subring {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPolyDeg_const (N := N) 0 a
  | insert j s hj ih =>
    have hj' := h j (Finset.mem_insert_self j s)
    have hs := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨p, hp, hPe⟩ := hj'
    obtain ⟨q, hq, hQe⟩ := hs
    refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
    have e := hQe g
    simp only at e
    show ∑ i ∈ insert j s, P i g = _
    rw [Finset.sum_insert hj, MvPolynomial.eval_add, ← hPe g, ← e]

private lemma mono_lemma {a b : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) (hab : a ≤ b) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem isPolyDeg_eval {σ : Type*} {a d : ℕ} (f : Matrix (Fin N) (Fin N) ℂ → σ → ℂ)
    (hf : ∀ i, U.IsPolyDeg a (fun g => f g i)) (q : MvPolynomial σ ℂ) (hq : q.totalDegree ≤ d) :
    U.IsPolyDeg (d * a) (fun g => MvPolynomial.eval (f g) q) := by
  classical
  have expand : (fun g => MvPolynomial.eval (f g) q) =
      fun g => ∑ m ∈ q.support, q.coeff m * ∏ i ∈ m.support, f g i ^ m i := by
    funext g
    rw [MvPolynomial.eval_eq]
  rw [expand]
  refine exists_pow_mul_finset_sum_mem_subring _ fun m hm => ?_
  have hdeg : (∑ i ∈ m.support, m i) * a ≤ d * a := by
    apply Nat.mul_le_mul_right
    exact (MvPolynomial.le_totalDegree hm).trans hq
  refine mono_lemma ?_ hdeg
  have hprod : U.IsPolyDeg (∑ i ∈ m.support, m i * a) (fun g => ∏ i ∈ m.support, f g i ^ m i) :=
    isPolyDeg_prod m.support (fun i => m i * a) (fun i => isPolyDeg_pow (hf i) (m i))
  rw [Finset.sum_mul]
  simpa using exists_pow_mul_mul_mem_subring (isPolyDeg_const (q.coeff m) 0) hprod

end GlobalTheory.WigSh.OmgContr

namespace GlobalTheory.WigSh

open OmgContr

theorem wigMap_omg : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (π' : Mx k r → (Wq →L[ℂ] Wq)) (π'' : Mx k r → (Wq' →L[ℂ] Wq')) (d : ℕ) (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → GlobalTheory.WigSh.WigMap k r z' π'' π' d A → (∃ (t : ℕ) (c : Fin t → Mx k r → ℂ) (L : Fin t → (Wq' →L[ℂ] Wq)), (∀ i, Formalism.FourierDecayAlt.U.IsPolyDeg (d * (r + 1)) (c i)) ∧ ∀ g, A (GlobalTheory.WigSh.omg k r z z' g) = ∑ i, c i g • L i) ∧ ∀ g ∈ UH (Hpk k r), ∀ p : Formalism.FourierDecayAlt.B.SS k r, Matrix.of p.1.1 ∈ UWset k r z → Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r → Matrix.of p.2.1 ∈ UWset k r z' → Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r → (A (GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g))).comp (π'' (Matrix.of p.2.1)⁻¹) = (π' (Matrix.of p.2.1)⁻¹).comp (A (GlobalTheory.WigSh.omg k r z z' g)) := by
  intro Wq _ _ Wq' _ _ k r z z' π' π'' d A hz hTz hz' hTz' hA
  obtain ⟨⟨t, q, Lm, hq, hAe⟩, hAeq, -, -⟩ := hA
  refine ⟨⟨t, fun i g => MvPolynomial.eval
      (Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) (q i), Lm, ?_, ?_⟩, ?_⟩
  · intro i
    refine isPolyDeg_eval (N := 2 * r + k + 1)
      (fun g => Sum.elim (GlobalTheory.WigSh.omg k r z z' g) (fun j => star (GlobalTheory.WigSh.omg k r z z' g j))) ?_ (q i) (hq i)
    rintro (j | j)
    · exact GlobalTheory.WigSh.omg_isPolyDeg k r z z' j
    · exact isPolyDeg_star (GlobalTheory.WigSh.omg_isPolyDeg k r z z' j)
  · intro g
    exact hAe _
  · intro g hg p h1 h2 h3 h4
    have hn : (Matrix.of p.1.2)⁻¹ * g ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hg
    have hG : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 ∈ UH (Hpk k r) :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hn h4.1
    have hs : Formalism.FourierDecayAlt.B.sgs p g =
        (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
      simp only [Formalism.FourierDecayAlt.B.sgs, Matrix.mul_assoc]
    have hom : GlobalTheory.WigSh.omg k r z z' (Formalism.FourierDecayAlt.B.sgs p g) =
        (Matrix.of p.2.1)⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' g := by
      rw [hs, GlobalTheory.WigSh.omg_equivariant k r z z' _ _ _ hz hTz hz' hTz' hG h1 h3,
        GlobalTheory.WigSh.omg_mul_N k r z z' _ _ hz hz' hn h4, GlobalTheory.WigSh.OmLeftN.omg_left_N k r z z' g _ hz hz' hg h2]
    rw [hom]
    exact hAeq _ (GlobalTheory.WigSh.OmgEquiv.inv_mem h3) _

end GlobalTheory.WigSh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
section
open Matrix

noncomputable section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private lemma deriv_smul_const_vec (φ : ℝ → ℂ) (v : E) (t : ℝ) :
    deriv (fun s => φ s • v) t = deriv φ t • v := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hφ : DifferentiableAt ℝ φ t
  · exact deriv_smul_const hφ v
  · have hn : ¬ DifferentiableAt ℝ (fun s => φ s • v) t := by
      intro h
      obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
      apply hφ
      have hv' : ℓ v ≠ 0 := by rw [hℓ]; simpa using hv
      have h2 := (((ℓ.restrictScalars ℝ).differentiableAt).comp t h).const_mul (ℓ v)⁻¹
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show φ s = (ℓ v)⁻¹ * ℓ (φ s • v)
      rw [map_smul, smul_eq_mul, mul_comm (φ s), ← mul_assoc, inv_mul_cancel₀ hv', one_mul]
    rw [deriv_zero_of_not_differentiableAt hφ, deriv_zero_of_not_differentiableAt hn, zero_smul]

private lemma Dx_smul_const (x : Bool × B.Mat k r) (f : B.Mat k r → ℂ) (v : E) :
    Dx x (fun g => f g • v) = fun g => Dx x f g • v := by
  funext g
  unfold Dx
  split_ifs
  · exact deriv_smul_const_vec _ v 0
  · exact deriv_smul_const_vec _ v 0

private lemma Dw_smul_const (w : List (Bool × B.Mat k r)) (f : B.Mat k r → ℂ) (v : E) :
    Dw w (fun g => f g • v) = fun g => Dw w f g • v := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w (fun g => f g • v)) = fun g => Dx x (Dw w f) g • v
    rw [ih]
    exact Dx_smul_const x _ v

theorem polyOK_star {N a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : IsPolyDeg a P) :
    IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hPq⟩ := h

  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact MvPolynomial.totalDegree_le_of_support_subset (MvPolynomial.support_map_subset (f := starRingEnd ℂ) q)
  · intro g

    have key : ∀ (p : MvPolynomial ((Fin N × Fin N) ⊕ (Fin N × Fin N)) ℂ) (y : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℂ),
        star (MvPolynomial.eval y p) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun i => star (y i)) p := by
      intro p y
      induction p using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.eval_C, MvPolynomial.eval₂_C, Complex.star_def]
      | add p p' hp hp' => rw [map_add (f := _), star_add, hp, hp', MvPolynomial.eval₂_add]
      | mul_X p i hp =>
        rw [map_mul, star_mul', hp, MvPolynomial.eval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    show star (P g) = _
    rw [MvPolynomial.eval_rename, MvPolynomial.eval_map, hPq g, key]
    congr 1
    funext i
    rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> simp

theorem polyOK_ck {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) (UU : Set (B.Mat k r)) :
    B.CkOn ⊤ UU (fun g => P g • v) := by
  obtain ⟨hs, -⟩ := polynomial_bound k r κ P hP
  intro g₀ _
  exact ⟨Set.univ, fun g => P g • v, isOpen_univ, Set.mem_univ _,
    (hs.smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩

theorem polyOK_bound {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) {d : ℝ} (hd : (κ : ℝ) ≤ d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r, ‖B.dLR u w (fun g => P g • v) g‖ ≤ C * B.gN g ^ d := by
  obtain ⟨-, hB⟩ := polynomial_bound k r κ P hP
  obtain ⟨C₀, hC₀⟩ := hB m
  refine ⟨max C₀ 0 * ‖v‖, mul_nonneg (le_max_right _ _) (norm_nonneg _), ?_⟩
  intro u w hu hw hl g hg
  have h1 := hC₀ u w hu hw hl g hg
  have hs : ((u ++ w).map (fun _ : B.Mat k r => (0 : ℕ))).sum = 0 := by simp
  rw [hs, Nat.cast_zero, add_zero, dLR_eq] at h1

  have hg1 : 1 ≤ B.gN g := gN_ge_one hg
  have e0 : 0 ≤ B.gN g ^ (κ : ℝ) := Real.rpow_nonneg (zero_le_one.trans hg1) _
  have hpow : B.gN g ^ (κ : ℝ) ≤ B.gN g ^ d := Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hC : ‖Dw (wL u ++ wR w) P g‖ ≤ max C₀ 0 * B.gN g ^ d :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) e0).trans
      (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
  rw [dLR_eq, Dw_smul_const, norm_smul]
  calc ‖Dw (wL u ++ wR w) P g‖ * ‖v‖ ≤ max C₀ 0 * B.gN g ^ d * ‖v‖ :=
        mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    _ = max C₀ 0 * ‖v‖ * B.gN g ^ d := by ring

end aux

private lemma foldr_max_zero_le_of_forall_le {o : ℕ} (l : List ℕ) (h : ∀ a ∈ l, a ≤ o) : l.foldr max 0 ≤ o := by

  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih => exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem polyOp_ok : Formalism.FourierDecayAlt.P.CutMP.JDPolyOK := by
  intro k r Wp Wq _ _ _ _ _ o κ Θ hΘ
  refine ⟨fun UU T hT => ?_, fun d hd T hT => ?_, ?_⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    exact ⟨polyOK_ck hP _ UU, polyOK_ck (polyOK_star hP) _ UU⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    refine ⟨polyOK_ck hP _ _, polyOK_ck (polyOK_star hP) _ _, fun m => ?_⟩
    obtain ⟨C₁, -, h₁⟩ := polyOK_bound hP (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    obtain ⟨C₂, -, h₂⟩ := polyOK_bound (polyOK_star hP) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    refine ⟨max C₁ C₂, fun u w hu hw hl g hg => ?_⟩
    have hx : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (zero_le_one.trans (gN_ge_one hg)) d
    exact ⟨(h₁ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx),
      (h₂ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)⟩
  · show (Θ.map fun T => T.word.length).foldr max 0 ≤ o
    refine foldr_max_zero_le_of_forall_le _ fun a ha => ?_
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ha
    exact (hΘ T hT).1

end GlobalTheory.HatNF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyOpExistsComposition
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PolyComp

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose MvPolynomial

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ}

def scalTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, inLie k r X) : DTerm k r Wp Wq where
  coef g := P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := w
  word_lie := hw
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner, PI.UnitaryGroupMassFormula.UsCompose.hsVec_smul,
      inner_smul_right, inner_smul_left, Complex.star_def, Complex.conj_conj]

end

end GlobalTheory.HatNF.PolyComp

namespace GlobalTheory.HatNF

open GlobalTheory.HatNF.PolyComp

end GlobalTheory.HatNF
end

