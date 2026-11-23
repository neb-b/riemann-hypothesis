module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import GroundTheory.AutomorphicForms.FourierWhittaker
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import GroundTheory.AutomorphicForms.ReductionFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesSplitPlaceReductionLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead.Red

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem ALint_eq : ReciprocityTheory.Aut.ALint L = Formalism.L2.Herm.intAf (maximalRealSubfield L) L := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), ⟨y, rfl⟩⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  · refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨y, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)

theorem proj_tmul_one (s : ReciprocityTheory.Aut.SplitPlace L) (y : L) :
    s.proj (y ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) = s.i y := by
  simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem proj_mem (s : ReciprocityTheory.Aut.SplitPlace L) {z : ReciprocityTheory.Aut.AL L} (hz : z ∈ ReciprocityTheory.Aut.ALint L) :
    s.proj z ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := by
  have hle : ReciprocityTheory.Aut.ALint L ≤ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap s.proj := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨y, rfl⟩ | ⟨c, hc, rfl⟩)
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, proj_tmul_one]
      exact s.split_le_one y
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      exact hc s.v
  exact hle hz

theorem proj_lt_one (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L)
    (hz : z ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) :
    Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, proj_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    have hc : Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (proj_mem s ((ALint_eq (L := L)).ge c.2))
    calc Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L))
        ≤ 1 * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L)) := by gcongr
      _ < 1 := by rwa [one_mul]

theorem resS_iff (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 ↔
      Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z)
  have e1 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) z :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := maximalRealSubfield L) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) (Formalism.L2.DIV.oToS (maximalRealSubfield L) L b) :=
    Ideal.quotientMap_mk
  have hmem : z - Formalism.L2.DIV.oToS (maximalRealSubfield L) L b ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) < 1 := by
    have := proj_lt_one s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, proj_tmul_one] at this
  rw [← hb, eq_comm (a := Ideal.Quotient.mk s.w.asIdeal b), Ideal.Quotient.eq]
  show _ ↔ Valued.v (s.i ((u - b : 𝓞 L) : L)) < 1
  have e : s.i ((u - b : 𝓞 L) : L) =
      (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) + (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
    ring
  constructor
  · intro h
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
  · intro h
    rw [← sub_eq_iff_eq_add] at e
    rw [← e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h h1)

def castE {F : Subfield L} (h : F = maximalRealSubfield L) :
    ReciprocityTheory.Aut.AL L ≃+* L ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (GlobalTheory.Mem.R3.swapCast h).symm.trans (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) L).toRingEquiv

theorem castE_rfl (x : ReciprocityTheory.Aut.AL L) : castE (L := L) rfl x = x :=
  (Algebra.TensorProduct.comm (maximalRealSubfield L) (ReciprocityTheory.Aut.AFplus L) L).apply_symm_apply x

theorem castE_mem_iff {F : Subfield L} (h : F = maximalRealSubfield L) (x : ReciprocityTheory.Aut.AL L) :
    castE h x ∈ Formalism.L2.Herm.intAf F L ↔ x ∈ ReciprocityTheory.Aut.ALint L := by
  subst h
  rw [castE_rfl, ALint_eq]

theorem resS_castE_iff {F : Subfield L} (h : F = maximalRealSubfield L) (s : ReciprocityTheory.Aut.SplitPlace L) (x : ReciprocityTheory.Aut.AL L)
    (z : Formalism.L2.Herm.intAf F L) (hz : (z : L ⊗[F] FiniteAdeleRing (𝓞 F) F) = castE h x) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj x) < 1 ↔ Formalism.L2.DIV.resS F s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  subst h
  rw [castE_rfl] at hz
  rw [← hz]
  exact resS_iff s z u

end General

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}

theorem frGL_one_val (y : GL (Fin m) (Formalism.L2.Herm.intAf F E)) (a c : Fin m) :
    (frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y).val a c = (y.val a c : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have h : frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y = intGL F E m y := by
    simp [frGL]
  rw [h]
  rfl

theorem mem_St_one (g : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) (h : ∀ a c, g.val a c ∈ Formalism.L2.Herm.intAf F E)
    (h' : ∀ a c, (g⁻¹).val a c ∈ Formalism.L2.Herm.intAf F E) : g ∈ St (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  have inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m := Fin m)) :=
    fun x y hxy => Matrix.ext fun a c => Subtype.ext (congrFun (congrFun hxy a) c)
  refine ⟨⟨Matrix.of fun a c => ⟨_, h a c⟩, Matrix.of fun a c => ⟨_, h' a c⟩, inj ?_, inj ?_⟩, ?_⟩
  · rw [map_mul, map_one]
    exact g.mul_inv
  · rw [map_mul, map_one]
    exact g.inv_mul
  · refine Units.ext (Matrix.ext fun a c => ?_)
    rw [frGL_one_val]
    rfl

end Stab

theorem red_eq_local : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → ∀ (hn : V.rank = n) (κ : GAf D.host.E n), (κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → ∀ a c : Fin V.rank, NX.locM s κ (Fin.cast hn a) (Fin.cast hn c) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧ ∀ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔ (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))).val a c = Ideal.Quotient.mk s.w.asIdeal u := by
  intro D V n hF P hP hn κ
  obtain ⟨hn', hP⟩ := hP
  have ent : ∀ (κ : GAf D.host.E n) a c, (Lev.finE V (P.ψ κ)).val a c =
      castE hF ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c)) := fun κ a c =>
    congrArg (Lev.swapAE D) (hP κ a c)
  have toSt : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) := fun hκ => by
    refine mem_St_one _ (fun a c => ?_) (fun a c => ?_)
    · rw [ent]
      exact (castE_mem_iff hF _).2 (hκ _ _)
    · rw [← map_inv, ← map_inv, ent]
      exact (castE_mem_iff hF _).2 (Subgroup.inv_mem _ hκ _ _)
  refine ⟨⟨toSt, ?_⟩, fun s hκ a c => ⟨proj_mem s (hκ _ _), fun u => ?_⟩⟩
  · rintro ⟨y, hy⟩ i j
    have h1 := ent κ (Fin.cast hn.symm i) (Fin.cast hn.symm j)
    rw [← hy, frGL_one_val] at h1
    exact (castE_mem_iff hF _).1 (h1 ▸ (y.val _ _).2)
  · obtain ⟨y, hy⟩ := toSt hκ
    have h1 := ent κ a c
    rw [← hy, frGL_one_val] at h1
    rw [← hy, redFn_frGL]
    exact resS_castE_iff hF s _ (y.val a c) h1 u

end GlobalTheory.MtRead.Red

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalWhittakerCoeffEqIteratedColumnTransform
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.WhitCols

open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E]

theorem avg_eq_setIntegral {ι : Type} [Fintype ι] (Φ : (ι → Ad E) → ℂ) (hΦ : Per (ratV E ι) Φ) :
    avg (ratV E ι) Φ = ∫ x in vecDomain E ι, Φ x ∂vecMeasure E ι := by
  have hF : IsAddFundamentalDomain (ratV E ι) (vecDomain E ι) (vecMeasure E ι) := isAddFundamentalDomain_vecDomain
  obtain ⟨-, -, -, h⟩ := GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι)
    (vecMeasure E ι) (vecDomain E ι) inferInstance hF Φ hΦ
  rw [h, vecMeasure_vecDomain]
  simp

def colIx {a k : ℕ} (hk : k < a) : Fin k ≃ UnipotentBlockColumnIndex a k k where
  toFun i := ⟨(⟨i.1, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  invFun t := ⟨t.1.1.1, t.2.1⟩
  left_inv i := rfl
  right_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp only at h1 h2 h3 ⊢
      omega

def colHom {a k : ℕ} (hk : k < a) : (Fin k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun x := fun t => x ((colIx hk).symm t)
  invFun y := fun i => y (colIx hk i)
  left_inv x := by funext i; simp
  right_inv y := by funext t; simp
  map_add' x y := rfl
  continuous_toFun := continuous_pi fun t => continuous_apply _
  continuous_invFun := continuous_pi fun i => continuous_apply _

theorem colHom_mem_iff {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    colHom hk x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (Fin k) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i => c (colIx hk i), funext fun i => ?_⟩
    have := congrFun hc (colIx hk i)
    simpa [colHom] using this
  · rintro ⟨c, rfl⟩
    exact ⟨fun t => c ((colIx hk).symm t), rfl⟩

theorem blkU_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    (blkU (colHom hk x) : GL (Fin a) (Ad E)) = colGL k x := by
  refine Units.ext ?_
  ext i j
  rw [blkU_apply]
  simp only [colGL, coe_uGL, uMat_apply, colX_apply, Matrix.one_apply, colHom, colIx]
  split_ifs <;> first | rfl | simp_all
  all_goals (exfalso; simp only [Fin.ext_iff, Fin.lt_def, Fin.le_def] at *; omega)

theorem dot_colHom {a k : ℕ} (hk : k < a) (x : Fin k → Ad E) :
    dot (eLast a k) (colHom hk x) = pair (lastVec k) x := by
  rw [dot, pair, ← (colIx hk).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [colHom, eLast, lastVec, colIx, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  by_cases h : (i : ℕ) + 1 = k <;> simp [h]

theorem colT_eq_stepCoeff {a k : ℕ} (hk : k < a) {F : GA E a → ℂ} (hc : Continuous F)
    (hl : ∀ (ξ : Fin k → E) g, F (AdelicGLn.diagonal E a (colGL k ξ) * g) = F g) (g : GA E a) :
    colT (GlobalTheory.StdCharConductor.psi E) k F g = stepCoeff k F g := by
  have hψ := GlobalTheory.StdCharConductor.stdPsi_psi E
  have hl' : ∀ (c : UnipotentBlockColumnIndex a k k → E) g, F (ratGL E a (blkU c) * g) = F g := by
    intro c g
    have e : ratGL E a (blkU c) = AdelicGLn.diagonal E a (colGL k (fun i => c (colIx hk i))) := by
      rw [ratGL_blkU, diagonal_colGL, ← blkU_colHom hk]
      congr 1
      funext t
      simp [colHom]
    rw [e, hl]
  have hP := per_coef hψ (eLast a k) hc hl' g
  have hP' : Per (ratV E (Fin k)) (fun x => (fun y : UnipotentBlockColumnIndex a k k → Ad E =>
      GlobalTheory.StdCharConductor.psi E (-dot (eLast a k) y) * F (blkU y * g)) (colHom hk x)) := by
    refine ⟨hP.1.comp (colHom hk).continuous_toFun, fun γ hγ x => ?_⟩
    simp only [map_add (f := _)]
    exact hP.2 _ ((colHom_mem_iff hk γ).2 hγ) _
  unfold colT coefF
  rw [← avg_equiv (Fin k → Ad E) (UnipotentBlockColumnIndex a k k → Ad E) (ratV E (Fin k)) (ratV E (UnipotentBlockColumnIndex a k k)) (isCoLat_ratV E _)
    (isCoLat_ratV E _) (colHom hk) (colHom_mem_iff hk) _ hP, avg_eq_setIntegral _ hP']
  unfold stepCoeff vecCoeff
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [blkU_colHom, dot_colHom, GlobalTheory.StdCharConductor.psi_apply]
  ring

def IsUU {j : ℕ} (h : Matrix (Fin j) (Fin j) E) : Prop :=
  ∀ i l : Fin j, l ≤ i → h i l = (1 : Matrix (Fin j) (Fin j) E) i l

theorem IsUU.isLastRowUnit {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) : IsLastRowUnit h := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · funext c; exact c.elim0
  · funext c
    have hc : c ≤ (⟨j - 1, by omega⟩ : Fin j) := by rw [Fin.le_def]; show (c : ℕ) ≤ j - 1; omega
    rw [vecMul_lastVec _ _ hj, hh _ _ hc, Matrix.one_apply]
    simp only [lastVec, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

omit [NumberField E] in
theorem isUU_blockMat {j : ℕ} {h : Matrix (Fin j) (Fin j) E} (hh : IsUU h) :
    IsUU (blockMat (n := j + 1) (Nat.le_succ j) h) := by
  intro i l hli
  rw [blockMat_apply]
  split_ifs with ha hb
  · rw [hh _ _ (by rw [Fin.le_def] at hli ⊢; exact hli), Matrix.one_apply, Matrix.one_apply]
    simp only [Fin.ext_iff]
  · exfalso; rw [Fin.le_def] at hli; omega
  all_goals simp_all [Matrix.one_apply]

omit [NumberField E] in
theorem isUU_colX {j : ℕ} (ξ : Fin j → E) : IsUU (uMat (colX (n := j + 1) j ξ)) := by
  intro i l hli
  rw [uMat_apply, Matrix.one_apply]
  split_ifs <;> first | rfl | (exfalso; simp only [Fin.lt_def, Fin.le_def] at *; omega)

theorem partialCoeff_uu {n : ℕ} {f : GA E n → ℂ}
    (hf : ∀ γ ∈ mirU E n 0, ∀ g, f (ratGL E n γ * g) = f g) :
    ∀ (m j : ℕ), n - j = m → ∀ (hj : j ≤ n) (h : GL (Fin j) E), IsUU (h : Matrix (Fin j) (Fin j) E) → ∀ g,
      partialCoeff f j (AdelicGLn.diagonal E n (blockGL hj h) * g) = partialCoeff f j g := by
  intro m
  induction m with
  | zero =>
    intro j hjm hj h hh g
    obtain rfl : j = n := by omega
    rw [partialCoeff_self]
    have : blockGL hj h = h := Units.ext (by rw [coe_blockGL]; exact blockMat_self _)
    rw [this]
    exact hf h (mem_mirU.2 fun i k _ hk => hh i k hk) g
  | succ m ih =>
    intro j hjm hj h hh g
    have hjn : j < n := by omega
    rw [partialCoeff_of_lt f hjn]
    have hB : ∀ g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (blockGL hjn.le h) * g) =
        partialCoeff f (j + 1) g := by
      intro g
      rw [← blockGL_blockGL (Nat.le_succ j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_blockMat hh) g
    have hC : ∀ (ξ : Fin j → E) g, partialCoeff f (j + 1) (AdelicGLn.diagonal E n (colGL j ξ) * g) =
        partialCoeff f (j + 1) g := by
      intro ξ g
      rw [colGL_eq_blockGL (Nat.lt_succ_self j) hjn]
      exact ih (j + 1) (by omega) hjn _ (isUU_colX _) g
    rw [stepCoeff_diagonal_blockGL hjn h hB hC g, hh.isLastRowUnit]
    rfl

theorem colT_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) {k : ℕ} (hk : k < m + 1) :
    colT (GlobalTheory.StdCharConductor.psi E) k (partialCoeff f (k + 1)) = partialCoeff f k := by
  funext g
  rw [partialCoeff_of_lt f hk]
  refine colT_eq_stepCoeff hk (continuous_partialCoeff hc _) (fun ξ g => ?_) g
  rw [colGL_eq_blockGL (Nat.lt_succ_self k) hk]
  exact partialCoeff_uu hf _ (k + 1) rfl hk _ (isUU_colX _) g

theorem whit_partialCoeff {m : ℕ} {f : GA E (m + 1) → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) :
    ∀ i, i ≤ m → GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) i (partialCoeff f (i + 1)) = partialCoeff f 1
  | 0, _ => rfl
  | i + 1, hi => by
    rw [GlobalTheory.CuspGeneric.whit_succ, colT_partialCoeff hc hf (by omega : i + 1 < m + 1),
      whit_partialCoeff hc hf i (by omega)]

theorem whit_eq_colWhit : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (f : GA E (m + 1) → ℂ), Continuous f →
    (∀ γ ∈ mirU E (m + 1) 0, ∀ g, f (ratGL E (m + 1) γ * g) = f g) →
    ∀ g, GlobalTheory.JSW.whit f g = GlobalTheory.CuspGeneric.whit (GlobalTheory.StdCharConductor.psi E) m f g := by
  intro E _ _ m f hc hf g
  rw [GlobalTheory.JSW.whit, whittaker_eq_partialCoeff hc (Nat.succ_pos m), ← whit_partialCoeff hc hf m le_rfl,
    partialCoeff_self]

end GlobalTheory.WhitCols
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSmoothDecayModerateGrowthRightTranslate
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RtGood

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def conjL (y : GL (Fin a) (Cinf E)) (X : Lie E a) : Lie E a := toL ((y⁻¹).val * Matrix.of X * y.val)

theorem lie_mul_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (X : Lie E a) :
    lie E a X * rt E a (infGL E a y * finGL E a k) = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by
  have h1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e] at h1
  have h2 := lie_rt_fin (conjL y X) k
  have h1' : lie E a X * rt E a (infGL E a y) = rt E a (infGL E a y) * lie E a (conjL y X) := h1.symm
  calc lie E a X * rt E a (infGL E a y * finGL E a k)
      = lie E a X * rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [map_mul, mul_assoc]
    _ = rt E a (infGL E a y) * (lie E a (conjL y X) * rt E a (finGL E a k)) := by rw [h1', mul_assoc]
    _ = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by rw [h2, map_mul, mul_assoc]

theorem word_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word l (rt E a (infGL E a y * finGL E a k) φ) =
      rt E a (infGL E a y * finGL E a k) (GlobalTheory.GLFin.word (l.map (conjL y)) φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, GlobalTheory.MSpanDecay.word_cons, GlobalTheory.MSpanDecay.word_cons, ih, ← Module.End.mul_apply,
      lie_mul_rt, Module.End.mul_apply]

theorem height_conj_le (y : GL (Fin a) (Cinf E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : GL (Fin a) (Cinf E), height (y⁻¹ * u * y) ≤ K * height u := by
  set M : ℝ := ‖rmul (toL y.val)‖ * ‖lmul (toL (y⁻¹).val)‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have key : ∀ u : GL (Fin a) (Cinf E), ‖toL (y⁻¹ * u * y).val‖ ≤ M * ‖toL u.val‖ := by
    intro u
    have e : toL (y⁻¹ * u * y).val = rmul (toL y.val) (lmul (toL (y⁻¹).val) (toL u.val)) := rfl
    rw [e, hM, mul_assoc]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  refine ⟨1 + M, by positivity, fun u => ?_⟩
  have hi : (y⁻¹ * u * y)⁻¹ = y⁻¹ * u⁻¹ * y := by group
  have k1 := key u
  have k2 := key u⁻¹
  have n1 := norm_nonneg (toL u.val)
  have n2 := norm_nonneg (toL (u⁻¹).val)
  unfold height
  rw [hi]
  nlinarith

theorem decays_rt {G : GA E a → ℂ} (hG : GlobalTheory.ShortVecDecay.Decays G) (h : GA E a) :
    GlobalTheory.ShortVecDecay.Decays (fun g => G (g * h)) := fun L hL C₀ hC₀ N => by
  obtain ⟨C, hC⟩ := hG L hL (C₀ * {h}) (hC₀.mul isCompact_singleton) N
  refine ⟨C, fun g c hc ξ hξ hm => ?_⟩
  have := hC g (c * h) (Set.mul_mem_mul hc (Set.mem_singleton h)) ξ hξ hm
  show ‖G (g * c * h)‖ ≤ _
  rw [mul_assoc]
  exact this

theorem growth_rt {G : GA E a → ℂ} (hG : GlobalTheory.MSpanDecay.Growth G) (h : GA E a) :
    GlobalTheory.MSpanDecay.Growth (fun g => G (g * h)) := by
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨K, hK0, hK⟩ := height_conj_le y
  intro g
  obtain ⟨C, N, hC⟩ := hG (g * (infGL E a y * finGL E a k))
  refine ⟨|C| * K ^ N, N, fun u => ?_⟩
  have hz : y * (y⁻¹ * u * y) = u * y := by group
  have e : g * infGL E a u * (infGL E a y * finGL E a k) =
      g * (infGL E a y * finGL E a k) * infGL E a (y⁻¹ * u * y) := by
    rw [mul_assoc g (infGL E a y * finGL E a k), mul_assoc (infGL E a y), ← infGL_comm (y⁻¹ * u * y) k,
      ← mul_assoc (infGL E a y), ← map_mul, hz, map_mul]
    simp only [mul_assoc]
  show ‖G (g * infGL E a u * (infGL E a y * finGL E a k))‖ ≤ _
  rw [e]
  have h1 := one_le_height u
  have h2 := hK u
  have h3 : 0 ≤ height (y⁻¹ * u * y) := (zero_le_one.trans (one_le_height _))
  calc _ ≤ C * height (y⁻¹ * u * y) ^ N := hC _
    _ ≤ |C| * height (y⁻¹ * u * y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 N)
    _ ≤ |C| * (K * height u) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (abs_nonneg C)
    _ = |C| * K ^ N * height u ^ N := by rw [mul_pow, mul_assoc]

theorem good_mul_right : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (h : GA E a), GlobalTheory.MSpanDecay.Good F → GlobalTheory.MSpanDecay.Good (fun g => F (g * h)) := by
  intro E _ _ _ a F h hF
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨hS, hl⟩ := hF
  refine ⟨rt_mem_Sm _ F hS, fun l => ?_⟩
  have e : (⟨fun g => F (g * (infGL E a y * finGL E a k)), rt_mem_Sm _ F hS⟩ : Sm E a) =
      rt E a (infGL E a y * finGL E a k) ⟨F, hS⟩ := rfl
  rw [e, word_rt]
  obtain ⟨hd, hg⟩ := hl (l.map (conjL y))
  exact ⟨decays_rt hd _, growth_rt hg _⟩

end GlobalTheory.RtGood

end
end

