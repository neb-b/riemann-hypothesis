module

public import Mathlib
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0004
public import Development.WeilBound.ThetaLifts.LatticeBasics.LocDistE
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.BoxSecX
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

def DblX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ dd om₂ S l, IsDbl (σ := σ) (A := W) (Y := X) (κ := (Fin n × Fin d) ⊕ (Fin n × Fin d)) B.ψ dd χW om₂ S l ∧
      (∀ Φ₁ ∈ schA F _, ∀ Φ₂ ∈ schA F _, boxFun Φ₁ (star Φ₂) ∈ schA F _ ∧ ∀ h g g' x, IsEmb g g' x →
        detInv χW g' * thetaSum F (om₂ x (S h (boxFun Φ₁ (star Φ₂)))) = theta om Φ₁ g h * star (theta om Φ₂ g' h) ∧
        detInv χW g' • om₂ x (boxFun Φ₁ (star Φ₂)) = boxFun (om (g, 1) Φ₁) (star (om (g', 1) Φ₂))) ∧
      IsDblCoordX M dd ∧
      ∀ ν : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ c' : ℝ, 0 < c' ∧
        ∀ Ψ₁ ∈ schA F _, ∀ Ψ₂ ∈ schA F _, l (boxFun Ψ₁ (star Ψ₂)) = c' * ∫ u, Ψ₁ u * star (Ψ₂ u) ∂ν

def BoxSecX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M, IsSec K χ (((d : ℂ) - n) / 2) (fun x => l (om x (boxFun Φ₁ (star Φ₂))))

def SWFullX : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', B.IsGood σ → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      ∃ U Ê, IsEisCont (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) U Ê ∧ (((d : ℂ) - n) / 2) ∈ U ∧
        ∀ x, Ê (((d : ℂ) - n) / 2) x = (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.ConstOfGood
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DeterminantProjection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem det_ne_zero_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := fun z => by
  obtain ⟨e, A, hA⟩ := h
  let q : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr e)
  have := congrArg Matrix.det (show (Aᵀ.submatrix id q * M.submatrix q q) * (A.map star).submatrix q id = Matrix.fromBlocks 1 0 0 (-1) by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; exact hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, z, mul_zero, zero_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

omit [NumberField E] in
theorem hermND_transpose {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : IsHermND σ X.Jᵀ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨fun i j => h.herm j i, fun z => det_ne_zero_of_sig (h.sig w) ?_⟩
  rw [Matrix.det_transpose] at z
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero]

omit [NumberField E] in
theorem mem_UG_of {J : Matrix (Fin n) (Fin n) E} {g : GL (Fin n) (AE F E)} :
    g ∈ UG (cA σ) (incM F J) ↔ g ∈ HR (AF F) σ Jᵀ := by
  change (g.1ᵀ * incM F J * g.1.map (cA σ) = incM F J) ↔ (g.1.map (sigR (AF F) σ))ᵀ * (incM F J)ᵀ * g.1 = (incM F J)ᵀ
  rw [← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
    show (cA σ : AE F E → AE F E) = sigR (AF F) σ from funext cA_eq]

def sec {A : Type} [CommRing A] (R : Matrix (Fin n) (Fin n) A) (h : R * R = R) : A →* Matrix (Fin n) (Fin n) A where
  toFun z := 1 + (z - 1) • R
  map_one' := by simp
  map_mul' a b := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, add_assoc, ← add_smul]
    congr 2
    ring

theorem su_mem (hS : GlobalTheory.Published.StrongApproxSU) (hc : IsCMExt F E σ) {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n)
    (L : Subgroup (UA σ X.J)) (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L) {v : Pl F}
    (hv : ∀ u ∈ UAt σ X (evFin F v), u ∈ L) {ε : AF F} {e : AE F E} (hε : GlobalTheory.Published.IsPlacesIdem ∅ {v} ε) (e1 : e * e = e)
    (e2 : e * sigR (AF F) σ e = 0) (e3 : e + sigR (AF F) σ e = algebraMap (AF F) (AE F E) ε) (g : UA σ X.J)
    (hg : (mat g).det = 1) : g ∈ L := by
  let ι : HA (AF F) σ X.Jᵀ → UA σ X.J := fun x => ⟨HA.mat _ _ _ x, mem_UG_of.2 (show HR (AF F) σ X.Jᵀ from x).2⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have z : ∀ t, evFin F v t = 0 → t * ε = 0 := fun t ht => by
    refine Prod.ext (funext fun w => (congrArg (t.1 w * ·) (hε.2.1 w (Finset.notMem_empty w))).trans (mul_zero _))
      (FiniteAdeleRing.ext _ fun u => ?_)
    by_cases hu : u = v
    · subst hu
      exact (congrArg (· * ε.2 u) ht).trans (zero_mul _)
    · exact (congrArg (t.2 u * ·) (hε.2.2.2 u fun x => hu (Finset.mem_singleton.1 x))).trans (mul_zero _)
  refine closure_minimal (t := ι ⁻¹' L) ?_ (hL.preimage hι) (hS F E σ hc n _ hn hJ ∅ {v} ε hε
    (GlobalTheory.Published.StrongApprox.not_isCompact_split σ hn hJ v ε (hε.2.2.1 v (Finset.mem_singleton_self v)) e e1 e2 e3)
    (⟨g.1, mem_UG_of.1 g.2⟩ : HR (AF F) σ X.Jᵀ) (GlobalTheory.Published.StrongApprox.mem_SUAdelic.2 hg))
  rintro _ ⟨γ, ⟨-, y, -, hy⟩, h, ⟨-, hh⟩, rfl⟩
  have h1 : ι γ ∈ L := hr ⟨y, hy⟩
  have h2 : ι h ∈ L := hv _ fun t ht => Matrix.ext fun i j => by
    refine (congrArg (t • ·) (hh i j).symm).trans ?_
    rw [← Algebra.smul_def, smul_smul, z t ht, zero_smul, Matrix.zero_apply]
  exact mul_mem h1 h2

theorem exists_sec (hc : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ Jᵀ) (hn : 1 ≤ n) :
    ∃ S : normOne (cA σ) →* UA σ J, Continuous S ∧ (∀ z, (mat (S z)).det = (z.1 : (AE F E)ˣ)) ∧
      (∀ z : normOne (cA σ), (∃ k : E, k ≠ 0 ∧ ((z.1 : (AE F E)ˣ) : AE F E) = inclR (F := F) (AF F) k) → S z ∈ ratU σ J) ∧
      ∀ (z : normOne (cA σ)) (t : AF F), t • (((z.1 : (AE F E)ˣ) : AE F E) - 1) = 0 → t • (mat (S z) - 1) = 0 := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hσ := GlobalTheory.UnitaryHeckeBaseChange.sig_sig hc
  obtain ⟨u, hu⟩ := exists_aniso (σ : E →+* E) hσ Jᵀ (fun i j => hJ.1 j i) hJ.2
  have ha := inv_mul_cancel₀ hu
  have hb : (σ : E →+* E) (hsq (σ : E →+* E) Jᵀ u)⁻¹ = (hsq (σ : E →+* E) Jᵀ u)⁻¹ := by
    rw [map_inv₀, sigma_hsq (σ : E →+* E) hσ _ fun i j => hJ.1 j i]
  generalize (hsq (σ : E →+* E) Jᵀ u)⁻¹ = b at ha hb
  let i : E →+* AE F E := inclR (F := F) (AF F)
  have hR := proj_idem' _ _ _ _ ha
  have hi : ∀ a, i ((σ : E →+* E) a) = sigR (AF F) σ (i a) := fun _ => rfl
  have hA : i b * hsq (sigR (AF F) σ) (Jᵀ.map i) (fun k => i (u k)) = 1 := by
    rw [← hsq_map i (σ : E →+* E) _ hi, ← map_mul, ha, map_one]
  have h1 := proj_unitary (sigR (AF F) σ) (GlobalTheory.UnitaryHeckeBaseChange.cA_cA hc) (Jᵀ.map i)
    (fun a b => (hi _).symm.trans (congrArg i (hJ.1 b a))) _ _ hA (by rw [← hi, hb])
  have h2 := det_proj' _ _ _ _ hA
  rw [← proj_map i (σ : E →+* E) (sigR (AF F) σ) hi] at h1 h2
  generalize proj (σ : E →+* E) Jᵀ u b = R at hR h1 h2
  have hR' : R.map i * R.map i = R.map i := by rw [← Matrix.map_mul, hR]
  have cS : Continuous (sec _ hR') := continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  refine ⟨((Units.map (sec _ hR')).comp (normOne (cA σ)).subtype).codRestrict _ fun z =>
    mem_UG_of.2 (h1 z.1 (by rw [← cA_eq, mul_comm]; exact mem_normOne.1 z.2)),
    ((Continuous.units_map _ cS).comp continuous_subtype_val).subtype_mk _, fun z => h2 _,
    fun z ⟨k, k0, hk⟩ => ⟨Units.map (sec _ hR) (Units.mk0 k k0), Units.ext (Matrix.ext fun a b => ?_)⟩, fun z t ht => ?_⟩
  · change i ((1 : Matrix _ _ E) a b + (k - 1) * R a b) =
      (1 : Matrix _ _ (AE F E)) a b + (((z.1 : (AE F E)ˣ) : AE F E) - 1) * i (R a b)
    rw [hk, map_add (f := _), map_mul, map_sub, map_one, Matrix.one_apply, Matrix.one_apply, apply_ite i, map_one, map_zero]
  · change t • (1 + (((z.1 : (AE F E)ˣ) : AE F E) - 1) • R.map i - 1) = 0
    rw [add_sub_cancel_left, ← smul_assoc, ht, zero_smul]

omit [NumberField E] in
theorem conj_mem_UAt {X : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {u : UA σ X.J} (hu : u ∈ UAt σ X ev) (g : UA σ X.J) :
    g⁻¹ * u * g ∈ UAt σ X ev := fun t ht => by
  have : mat (g⁻¹ * u * g) - 1 = mat g⁻¹ * (mat u - 1) * mat g := by
    rw [mul_sub, sub_mul, mul_one]
    exact congrArg₂ (· - ·) rfl (Units.inv_mul g.1).symm
  rw [this, ← smul_mul_assoc, ← mul_smul_comm, hu t ht, mul_zero, zero_mul]

theorem mem_of_good (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (hc : IsCMExt F E σ)
    [IsGalois ℚ E] {X : Spc F E n} (hJ : IsHermND σ X.Jᵀ) (hn : 2 ≤ n) (T : Finset (Pl F)) (L : Subgroup (UA σ X.J))
    (hL : IsClosed (L : Set (UA σ X.J))) (hr : ratU σ X.J ≤ L)
    (hv : ∀ v ∉ T, SplitsFully E v → ∀ u ∈ UAt σ X (evFin F v), u ∈ L) (g : UA σ X.J) : g ∈ L := by
  obtain ⟨v, a, b, ε, e, hε, e1, e2, e3⟩ := exists_split hH hc T
  obtain ⟨S, cS, s1, s2, s3⟩ := exists_sec hc hJ (by omega)
  have hg : IsUnit (incM F X.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ (Matrix.det_transpose X.J ▸ hJ.2)).map _
  let z : normOne (cA σ) := ⟨_, det_mem_normOne ⟨fun a b => congrArg (inclR (F := F) (AF F)) (hJ.1 b a), hg⟩ g⟩
  have h1 : S z ∈ L := normOne_mem hH hc T (L.comap S) (hL.preimage cS) (fun z h => hr (s2 z h))
    (fun v a b z hz => hv v a b _ fun t ht => s3 z t (hz t ht)) z
  have h2 : g * S z⁻¹ ∈ L := su_mem hS hc hJ hn L hL hr (hv v a b) hε e1 e2 e3 _ (by
    rw [show mat (g * S z⁻¹) = mat g * mat (S z⁻¹) from rfl, Matrix.det_mul, s1]
    exact z.1.mul_inv)
  simpa using mul_mem h2 h1

theorem constOfGood_of (hS : GlobalTheory.Published.StrongApproxSU) (hH : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) : ConstOfGood := by
  intro F E _ _ _ _ _ σ B n X r s hB hX hn T f hf hr hv g
  have := hB.galois
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  let L : Subgroup (UA σ X.J) :=
    { carrier := ⋂ g, {x | f (x * g) = f g}
      one_mem' := Set.mem_iInter.2 fun g => congrArg f (one_mul g)
      mul_mem' := fun {a b} ha hb => Set.mem_iInter.2 fun g =>
        (congrArg f (mul_assoc a b g)).trans ((Set.mem_iInter.1 ha _).trans (Set.mem_iInter.1 hb _))
      inv_mem' := fun {a} ha => Set.mem_iInter.2 fun g =>
        (Set.mem_iInter.1 ha _).symm.trans (congrArg f (mul_inv_cancel_left a g)) }
  have := mem_of_good hS hH hB.cm (hermND_transpose hX) hn T L
    (isClosed_iInter fun g => isClosed_eq (hf.comp (continuous_mul_const g)) continuous_const)
    (fun γ h => Set.mem_iInter.2 (hr γ h)) (fun v a b u hu => Set.mem_iInter.2 fun g =>
      (congrArg f (by group)).trans (hv v a b _ (conj_mem_UAt hu g) g)) g
  exact (congrArg f (mul_one g)).symm.trans (Set.mem_iInter.1 this 1)

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

variable {Y : Spc F E n} {A : Spc F E m}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def SplitModel : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinW B.ψ t 1 1 ι) ∧ ∀ ι, M.IsLinW B.ψ t 1 1 ι →
      ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)),
        g₀.1 = (mat g).map (piW t) → h₀.1 = (mat h).map (piW t) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (g, h)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ)

def coef {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _)) (Φ : Fn F n d)
    (g : UA σ X.J) : ℂ := ∫ u, om (g, 1) Φ u * star (Φ u) ∂ν

def zint {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (ν : @Measure (Fin n × Fin d → AF F) (borel _))
    (a : G2 σ X → ℝ) (e : UA σ X.J × UA σ X.J →* G2 σ X) (Φ : Fn F n d) (s : ℂ) (g : UA σ X.J) : ℂ :=
  (a (e (g, 1)) : ℂ) ^ (s - ((d : ℂ) - n) / 2) * coef om ν Φ g


variable (σ Y) in
def locGrp (v : Pl F) : Subgroup (UA σ Y.J) := Subgroup.closure (UAt σ Y (evFin F v))

def IntAt (v : Pl F) (g : UA σ Y.J) : Prop :=
  ∀ z ∈ latHat Y, At (evFin F v) z → mat g *ᵥ z ∈ latHat Y ∧ mat g⁻¹ *ᵥ z ∈ latHat Y

def OffAt (v : Pl F) (g : UA σ Y.J) : Prop := (mat g).map (compFin F E v) = 1

def IsSphAt (K : Subgroup (G2 σ Y)) (χ : Chr F E) (v : Pl F) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t, IsPar p t → At (evFin F v) (mat2 p - 1) → ∀ k ∈ K, At (evFin F v) (mat2 k - 1) →
    f (p * k) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) * ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z


open Classical in
variable (E) in
def locD (n : ℕ) (v : Pl F) (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n, (1 - (if Nonempty (E →ₐ[F] Fv F v) then 1 else -1) ^ (n - (i + 1)) *
    (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * s + (i + 1 : ℕ))))⁻¹

def NormZeta : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∃ (U : Set ℂ) (Z : ℂ → ℂ) (t₀ : ℝ),
      IsOpen U ∧ (∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) ∧ ((d : ℂ) - n) / 2 ∈ U ∧ DifferentiableOn ℂ Z U ∧
      (∀ z : ℂ, t₀ < z.re → z ∈ U ∧ Integrable (zint om ν a e Φ z) M.μ ∧ Z z = ∫ g, zint om ν a e Φ z g ∂M.μ) ∧
      (M.I om Φ = 0 → Z (((d : ℂ) - n) / 2) = 0)

def EulerProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (T : Finset (Pl F)) (μ : Measure (UA σ Y.J)),
    μ.IsHaarMeasure → ∀ (μl : ∀ v, Measure (locGrp σ Y v)), (∀ v, (μl v).IsHaarMeasure ∧ μl v {g | IntAt v g.1} = 1) →
    ∀ (f : UA σ Y.J → ℂ) (fl : Pl F → UA σ Y.J → ℂ), Integrable f μ →
      (∀ v ∉ T, (∀ u ∈ locGrp σ Y v, ∀ g, OffAt v g → f (u * g) = fl v u * f g) ∧ (∀ u ∈ locGrp σ Y v, IntAt v u → fl v u = 1) ∧
        Integrable (fun u : locGrp σ Y v => fl v u.1) (μl v)) →
      Tendsto (fun S : Finset {v : Pl F // v ∉ T} => (∏ v ∈ S, ∫ u, fl v.1 u.1 ∂μl v.1) * ∫ g in {g | ∀ v ∉ T, IntAt v g}, f g ∂μ)
        atTop (𝓝 (∫ g, f g ∂μ))

def LocMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ v,
    ∃ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure ∧ μ {g | IntAt v g.1} = 1

def LocUnr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

def BadFactor : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → min r' s' = 0 → n ≤ d → Even d → ∀ T : Finset (Pl F), T ⊆ B.P → UnrOff χX (T : Set (Pl F)) →
    UnrOff χW (T : Set (Pl F)) → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → (∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀) →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∃ Φ ∈ PolData B M,
      (∀ (z : ℂ), ∀ v ∉ T, ∃ f, IsSphAt K χW v (z + n / 2) f ∧ ∀ u ∈ locGrp σ X v, (IntAt v u → f (e (u, 1)) = 1) ∧
        ∀ g, OffAt v g → zint om ν a e Φ z (u * g) = f (e (u, 1)) * zint om ν a e Φ z g) ∧
      Differentiable ℂ (fun z => ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ z g ∂M.μ) ∧
      ∫ g in {g | ∀ v ∉ T, IntAt v g}, zint om ν a e Φ (((d : ℂ) - n) / 2) g ∂M.μ ≠ 0

def RealInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → min r s = 0 → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] [Nontrivial P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P),
    RealQuot B M om p → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∀ k ∈ KInf σ X B.emb, Acts (evI F) (om (k, 1)) f₀ f₀

def DProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (T : Finset (Pl F)), ∃ d : ℂ → ℂ,
    DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re → d z ≠ 0 ∧
      HasProd (fun v : {v : Pl F // v ∉ T} => locD E n v.1 z) (d z)

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def SiegelWeilAniso : Prop := SWAniso ∧ SWAnisoX


variable (σ Y) in
def IsFrame2 (b : GL (Fin n ⊕ Fin n) E) : Prop :=
  (∃ ε : ℤˣ, b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ∧
    ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1


variable (F E) in
def intHat : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}


variable (F) in
def finOne : AF F := LinearMap.inr F (Ainf F) (Af F) 1

def inFrame (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
  incM F (b⁻¹).1 * mat2 x * incM F b.1

def IsStdK (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) : Prop :=
  ∀ k, k ∈ K ↔ (∀ w, (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1) ∧
    ∀ k' ∈ ({k, k⁻¹} : Set (G2 σ Y)), ∀ i j, finOne F • inFrame b k' i j ∈ intHat F E


variable (σ Y) in
def modFun : Submodule ℂ (G2 σ Y → ℂ) :=
  Submodule.span ℂ {f | Continuous f ∧ ∃ N : ℕ, ∀ x, ‖f x‖ ≤ (ht2 x : ℝ) ^ N}

def IsGrowForm (μ : modFun σ Y →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ f : modFun σ Y, (∀ x, ‖f.1 x‖ ≤ (ht2 x : ℝ) ^ N) → ‖μ f‖ ≤ C

def EisBL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U

def FrameConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → ∃ b K₀ p t, IsFrame2 σ Y b ∧ IsStdK B b K₀ ∧ IsPar p t ∧ ∀ k, k ∈ K ↔ p⁻¹ * k * p ∈ K₀

end GlobalTheory.ThK.Dbl

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocDist
section
namespace GlobalTheory.ThK.Dbl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel

theorem locDist : LocDist := by
  intro F _ _ v n d ξ hξ l hl
  have : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v
  have : LocallyCompactSpace (Fv F v) := inferInstance
  have : NonarchimedeanAddGroup (Fv F v) := by
    refine ⟨fun U hU => ?_⟩
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
    exact ⟨⟨(Valued.v.restrict.ltAddSubgroup γ), Valued.isOpen_ball _ _⟩, hγ⟩
  refine ⟨fun h => LD.lt_case ξ _ hξ h l hl, ?_⟩
  rintro rfl φ hφ g
  exact LD.eq_case ξ _ hξ l hl g φ hφ

end GlobalTheory.ThK.Dbl
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.OffOpenAlt
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def OffOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsSkew σ B r s →
    ∀ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, (∀ h h', IsEmb h h' (e (h, h'))) → ∀ γ ∈ rat2 σ Y,
      (¬ ∃ δ ∈ ratU σ Y.J, γ * (e (1, δ))⁻¹ ∈ par2 σ Y) →
      ∃ U : Submodule E (Fin n → E), U ≠ ⊥ ∧ (∀ u ∈ U, ∀ u' ∈ U, form σ Y.J u u' = 0) ∧
        (∀ m ∈ PositivityTheory.ThKEnd.unipU σ Y U, ∃ t, IsPar (γ * e (1, m) * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
          Matrix.GeneralLinearGroup.det m.1 = 1) ∧
        ∀ δ ∈ ratU σ Y.J, γ * e (1, δ) * γ⁻¹ ∈ par2 σ Y → ∀ m ∈ PositivityTheory.ThKEnd.unipU σ Y U, δ * m * δ⁻¹ ∈ PositivityTheory.ThKEnd.unipU σ Y U

def HtEmb : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n),
    ∃ C : ℝ≥0, (∀ h h' x, IsEmb (σ := σ) (Y := Y) h h' x → ht2 x ≤ C * (ht h * ht h')) ∧
      (∀ h h' : UA σ Y.J, ht (h * h') ≤ C * (ht h * ht h')) ∧ ∀ h : UA σ Y.J, 1 ≤ ht h

end GlobalTheory.ThK.Dbl

end
end

