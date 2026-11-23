module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLevelFormsIffStdGroupTypeSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBasePointUnitaryNormalisesLevel
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

section Small
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem row_small_of_mul_eq_one {P : HeightOneSpectrum (𝓞 E)} {n : ℕ} (l : Fin n) (M N : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hMN : M * N = 1) (hN : ∀ i j, Valued.v (N i j) ≤ 1) (hM : ∀ j, j ≠ l → Valued.v (M l j) < 1)
    (hl : Valued.v (M l l) = 1) (j : Fin n) (hj : j ≠ l) : Valued.v (N l j) < 1 := by
  have e := congrFun (congrFun hMN l) j
  rw [Matrix.mul_apply, Matrix.one_apply_ne (Ne.symm hj), ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at e
  have e2 : M l l * N l j = -∑ i ∈ Finset.univ.erase l, M l i * N i j := eq_neg_of_add_eq_zero_left e
  have h3 : Valued.v (∑ i ∈ Finset.univ.erase l, M l i * N i j) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun i hi => by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hN i j)) (hM i (Finset.ne_of_mem_erase hi))
  have h4 := congrArg Valued.v e2
  rw [Valuation.map_neg, map_mul, hl, one_mul] at h4
  rw [h4]
  exact h3

theorem val_eq_one_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c)
    (hc : c ≠ 0) : Valued.v z = 1 := by
  obtain ⟨r, rfl, hr⟩ := h
  have hr0 : r ∉ P.asIdeal := fun h0 => hc (Ideal.Quotient.eq_zero_iff_mem.2 h0)
  have ha : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
    rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hr0
  have e : z = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r) +
      (z - algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) := by ring
  rw [e, Valuation.map_add_eq_of_lt_left _ (by rw [ha]; exact hr), ha]

theorem prV_sigR_eq (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  | tmul a b => simp [prV, sigR]

variable [StarRing E]

theorem bc_prV_mem_UPts (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (AfE F E)}
    (hk : k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := by
  have hg' : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR hc.sig (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR_eq]
  have hJ : ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [Matrix.one_apply]
  rw [h1, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

end Small

theorem map_conj_levStab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST : Finset (Pl E)) (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (E ⊗[F] v.adicCompletion F)), k ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → k ∈ stabGL (baseDualV hc n ST v) → k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj k).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST v k hU h1 h2 h3
  have key : ∀ g : GL (Fin n) (E ⊗[F] v.adicCompletion F), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) →
      g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) → g ∈ stabGL (baseDualV hc n ST v) →
      g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) →
      ∀ x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v),
      g * x * g⁻¹ ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
    intro g gU gL gD gK x hx
    have hgl : g ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) := Subgroup.mem_inf.2 ⟨gU, gL⟩
    obtain ⟨hxl, hxD, hxf⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgl hxl) (inv_mem hgl), ⟨mul_mem (mul_mem gD hxD) (inv_mem gD), fun y => ?_⟩⟩
    have hz : ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) ∈
        baseDualV hc n ST v := ((inv_mem gD : g⁻¹ ∈ stabGL (baseDualV hc n ST v)) _).1 y.2
    have h4 := hxf ⟨_, hz⟩
    simp only [fLoc, Submodule.mkQ_apply] at h4 ⊢
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at h4 ⊢
    simp only [Submodule.coe_subtype, Submodule.coe_sub] at h4 ⊢
    have e : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) -
        (y : Fin n → E ⊗[F] v.adicCompletion F) =
        (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) -
          ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F)) := by
      have e1 : (g : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F)) = (y : Fin n → E ⊗[F] v.adicCompletion F) := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have e2 : ((g * x * g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ (y : Fin n → E ⊗[F] v.adicCompletion F) =
          (g : Matrix (Fin n) (Fin n) _) *ᵥ ((x : Matrix (Fin n) (Fin n) _) *ᵥ (((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) _) *ᵥ
          (y : Fin n → E ⊗[F] v.adicCompletion F))) := by
        simp only [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [Matrix.mulVec_sub, e2, e1]
    rw [e]
    exact (gK _).1 h4
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key k hU h1 h2 h3 x hx
  · intro x hx
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · have := key k⁻¹ (inv_mem hU) (inv_mem h1) (inv_mem h2) (inv_mem h3) x hx
      rwa [inv_inv] at this
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group


set_option maxHeartbeats 1000000 in
theorem basePt_facts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (k : GL (Fin n) (AfE F E)) (c : DiaG (E := E) (ST := ST)), (∃ p₀ : DecoF E n ∅ ∅ ∅, IsPtOf hc k p₀ ∧ p₀.deco.1.N = stdLat E n) → (∀ (P : ST) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then (c P : 𝓞 E ⧸ P.1.asIdeal) else 0)) → k ∈ UAd hc n ∧ (∀ v, bc (prV (E := E) v) k ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) ∧ (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, k.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) ∧ ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) k)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v) := by
  intro F E _ _ _ _ _ _ hc n _ ST π hB k c ⟨p₀, hk, hk0⟩ hrow
  classical
  have hl : (lastIdx n).1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))
  have hU : k ∈ UAd hc n := hk.uni
  have hkc := hk.lat
  rw [hk0] at hkc
  have hsingle : ∀ j, (Pi.single j 1 : Fin n → AfE F E) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := fun j => by
    refine (mem_latS_std _).2 fun i => ?_
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  have hInv : ∀ i j, ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have := (mem_latS_std _).1 ((hkc _).1 (hsingle j)) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hK : ∀ i j, ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ Formalism.L2.Herm.intAf F E :=
    fun i j => by
      have h1 : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((k : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hsingle j
      have := (mem_latS_std _).1 ((hkc _).2 h1) i
      rw [Matrix.mulVec_single_one] at this; exact this
  have hvI : ∀ (P : HeightOneSpectrum (𝓞 E)) (y : AfE F E), y ∈ Formalism.L2.Herm.intAf F E → Valued.v (adAt F P y) ≤ 1 :=
    fun P y hy => (mem_rInt_iff F E y).1 hy P
  have hsm : ∀ P ∈ ST, ∀ j, j ≠ lastIdx n →
      Valued.v (adAt F P ((k : Matrix (Fin n) (Fin n) (AfE F E)) (lastIdx n) j)) < 1 := by
    intro P hP j hj
    have hr := fun j' => hrow ⟨P, hP⟩ (lastIdx n) j' hl
    refine row_small_of_mul_eq_one (lastIdx n) (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P))
      ((k : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P)) ?_ (fun i j => hvI P _ (hK i j)) (fun j' hj' => ?_) ?_ j hj
    · rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have := hr j'
      rw [if_neg hj'] at this
      exact DilPt.hasRes_lt_one this
    · have h5 := hr (lastIdx n)
      rw [if_pos rfl] at h5
      have := P.isPrime
      exact val_eq_one_of_hasRes h5 (Units.ne_zero _)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) k ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧
      bc (prV (E := E) v) k ∈ stabGL (baseDualV hc n ST v) ∧
      bc (prV (E := E) v) k ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
    intro v
    refine GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices hc n hB v _ (bc_prV_mem_UPts hc v hU)
      ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hK i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hK _ j) (fun P hP => hsm P hP j hj)⟩ ?_
    rw [← map_inv]
    refine ⟨fun i j => Formalism.UG.P.afsplit_prV_int v _ (hInv i j), fun j hj => GlobalTheory.T.placeProjection_eq_basePi_mul_integral hB v _ (hInv _ j) (fun P hP => ?_)⟩
    have := hrow ⟨P, hP⟩ (lastIdx n) j hl
    rw [if_neg hj] at this
    exact DilPt.hasRes_lt_one this
  refine ⟨hU, fun v => ⟨bc_prV_mem_UPts hc v hU, (hloc v).1⟩, fun x => ?_,
    fun v _ => map_conj_levStab hc n ST v _ (bc_prV_mem_UPts hc v hU) (hloc v).1 (hloc v).2.1 (hloc v).2.2⟩
  rw [GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST), GlobalTheory.LatLocGlob.mem_latS_adele_iff _ (baseLb_fin n ST)]
  refine forall_congr' fun v => ?_
  have e : (fun i => prV (E := E) v ((k.1 *ᵥ x) i)) =
      ((bc (prV (E := E) v) k : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun i => prV (E := E) v (x i) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  rw [e]
  exact ((hloc v).1 _).symm

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartCharacterFramesOnPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

theorem chr_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (σ : X.K →+* ℂ) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)) (D : ∀ P : Q, Set (Sp X.E n)) (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g : GL (Fin n) (AfE X.F X.E)} (z : levUQ hc n ST SG Q (chG Λ C) q), g ∈ UAd hc n → ∀ (κ : FrmG Λ Θ), ufGL X.E n κ.1 = 1 → FrExact q g r.1.1 → FrExact q (g * z.1) (ya Λ Θ κ r).1.1 → ((((levTyp (chLam σ Λ C)).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ)⁻¹ : levUQ hc n ST SG Q (chG Λ C) q →* ℂˣ) z : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K) := by
  intro X n ST SG Q y _ hc σ Λ Θ r C D q g z hg κ h1 hE hE'
  obtain ⟨γ, h, θ⟩ := κ
  have hγ : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
  subst hγ

  have hzU : z.1 ∈ levU hc n ST SG (chG Λ C) := levUQ_le q _ z.2
  have hx : g * z.1 ∈ UAd hc n := mul_mem hg (levU_le_UAd hc n ST SG _ hzU)
  have hdeco : decoOf ST SG (g * z.1) = ((1, h.1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) • decoOf ST SG g := by
    rw [hE'.1, hE.1]
    rfl
  have e2 : decoRaw ST SG (g * z.1) = (decoRaw ST SG g).act 1 h.1 := by
    rw [← rlc_decoOf_val hc n ST SG hx, ← rlc_decoOf_val hc n ST SG hg, hdeco]
    rfl
  obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hx hg h.1 e2
  have e3 : z.1 = ((g * z.1)⁻¹ * g)⁻¹ := by group
  have hJ' : z.1 ∈ J0 hc n ST := e3 ▸ inv_mem hJ
  have hr' : redG hc n ST SG ⟨z.1, hJ'⟩ = h.1⁻¹ := by
    rw [← hr, ← map_inv]
    exact congrArg _ (Subtype.ext e3)
  have hA : levTyp (chLam σ Λ C) (Subgroup.inclusion (levUQ_le q _) z) = (Units.map σ.toMonoidHom (Λ.chr h)) := by
    have h2 : Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ (Subgroup.inclusion (levUQ_le q _) z)) = h⁻¹ :=
      Subtype.ext hr'
    show (Units.map σ.toMonoidHom (Λ.chr (Subgroup.inclusion (chG_le Λ C) (Formalism.L2.Col.levRed hc n ST SG _ (Subgroup.inclusion (levUQ_le q _) z)))))⁻¹ = _
    rw [h2, map_inv, map_inv, inv_inv]

  have hP : ∀ P : Q, q.at P z.1 = Formalism.UG.bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) := fun P => by
    have a1 := hE.2 P
    have a2 := hE'.2 P
    have efr : (ya Λ Θ ((1 : UF X.E n), h, θ) r).1.1.fr P = r.1.1.fr P * ((θ.1 P)⁻¹).1 := by
      show (1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) * r.1.1.fr P * ((θ.1 P)⁻¹).1 = _
      rw [one_mul]
    have a3 : q.at P (g * z.1) = q.at P g * q.at P z.1 := by
      simp only [QLoc.at, map_mul]
    rw [a3, a1, efr] at a2
    simp only [qGL, map_mul] at a2
    exact mul_left_cancel a2
  have hB : ∀ P : Q, q.chr P (lqRes q (chG Λ C) P z) = ((Θ P).lam ⟨θ.1 P, θ.2 P trivial⟩)⁻¹ := fun P => by
    have hmem : Formalism.UG.bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) ∈ q.U P := hP P ▸ (lqRes q (chG Λ C) P z).2
    have hcut : (θ.1 P)⁻¹ ∈ (cutQ Θ D P).H := (q.U_rat P _).1 hmem
    have e4 : lqRes q (chG Λ C) P z = ⟨_, hmem⟩ := Subtype.ext (hP P)
    rw [e4, q.chr_rat P _ hcut hmem, ← map_inv]
    rfl
  have hT : Θ.chr θ = ∏ P : Q, (Θ P).lam ⟨θ.1 P, θ.2 P trivial⟩ := by
    unfold LevQFam.chr piChar
    erw [MonoidHom.finsetProd_apply]
    rfl
  have hC : chiQ q (chG Λ C) σ z = (Units.map σ.toMonoidHom (Θ.chr θ))⁻¹ := by
    unfold chiQ
    rw [MonoidHom.finsetProd_apply, hT, map_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hB P, map_inv]
  show ((levTyp (chLam σ Λ C) (Subgroup.inclusion (levUQ_le q _) z) * (chiQ q (chG Λ C) σ z)⁻¹ : ℂˣ) : ℂ) = _
  rw [hA, hC, inv_inv, ← map_mul]
  rfl

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassStabiliserRationalParts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.ChEx.stM_range_tw : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → ∀ (c : (stR Λ Θ p₀ pref).Cl) (b : β), c.1 = b → ∀ (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar (rp Λ Θ p₀ pref c) = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq (rp Λ Θ p₀ pref c) = D → ∀ (γ : GL (Fin n) X.E), (γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × ↥(chG (Λ b) C) × ↥(GlobalTheory.Mem.Col2.ChEx.cutQ (Θ b) D).grp, ufGL X.E n g.1 = γ ∧ g • (rp Λ Θ p₀ pref c).1.1 = (rp Λ Θ p₀ pref c).1.1) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq hI hD c b hb C hC D hD2 γ
  have img : ∀ (θ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (C : Set (Sp X.E n)), (fun v => θ v) '' C = C ↔ ∀ v, θ v ∈ C ↔ v ∈ C := by
    intro θ C
    constructor
    · intro h v
      constructor
      · intro hv
        rw [← h] at hv
        obtain ⟨w, hw, e⟩ := hv
        rwa [← θ.injective e]
      · intro hv
        rw [← h]
        exact ⟨v, hv, rfl⟩
    · intro h
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (h w).2 hw
      · intro hv
        refine ⟨θ.symm v, (h _).1 ?_, θ.apply_symm_apply v⟩
        rwa [θ.apply_symm_apply]
  subst hb hC hD2
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    replace hg : ya (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c := hg
    have hq : ∀ P, g.2.2.1 P ∈ GlobalTheory.Mem.Col2.ChEx.frStab P.1 (cq (rp Λ Θ p₀ pref c) P) := fun P => by
      have h := hI (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) P
      rw [hg] at h
      exact GlobalTheory.Mem.Col2.ChEx.mem_frStab.2 ((img _ _).1 h.symm)
    refine ⟨(g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, (bar_ya_eq_iff _ _ _ _).1 (congrArg bar hg)⟩⟩,
      ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.2 ⟨g.2.2.2, hq⟩⟩), rfl, ?_⟩
    exact congrArg (fun q : PtY ST SG Q y => q.1.1) hg
  · rintro ⟨g, rfl, hg⟩
    have hq := (GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.1 g.2.2.2).2
    refine ⟨⟨(g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.cutQ_grp_le _ _ g.2.2.2⟩), ?_⟩, rfl⟩
    show ya (Λ c.1) (Θ c.1) _ (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c
    refine hD _ _ hg ((bar_ya_eq_iff _ _ _ _).2 (mem_chG.1 g.2.1.2).2) ?_
    funext P
    rw [hI]
    exact (img _ _).2 (GlobalTheory.Mem.Col2.ChEx.mem_frStab.1 (hq P))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartClassesBijectiveOrbitsFramedLattices
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section OrbF

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}

theorem image_eq_iff_frStab {P : HeightOneSpectrum (𝓞 X.E)} (C : Set (Sp X.E n)) (g : ↥(GLint X.E n P)) :
    (fun v => g.1 v) '' C = C ↔ g ∈ frStab P C := by
  rw [mem_frStab]
  constructor
  · intro e v
    constructor
    · intro hv
      rw [← e] at hv
      obtain ⟨u, hu, huv⟩ := hv
      rwa [← g.1.injective huv]
    · intro hv
      rw [← e]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h u).2 hu
    · intro hv
      refine ⟨g.1.symm v, (h _).1 ?_, LinearEquiv.apply_symm_apply g.1 v⟩
      rw [LinearEquiv.apply_symm_apply]
      exact hv

def frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) : FrmG Λ Θ :=
  (g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, cutQ_grp_le _ _ g.2.2.2⟩)

theorem ya_frLift (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal))
    (D : ∀ P : Q, Set (Sp X.E n)) (g : UF X.E n × chG Λ C × (cutQ Θ D).grp) (q : PtY ST SG Q y) :
    (ya Λ Θ (frLift Λ Θ C D g) q).1.1 = g • q.1.1 := rfl

end OrbF

end GlobalTheory.Mem.Col2.ChEx

namespace GlobalTheory.Mem.Col2.ChEx

theorem clsF_bij : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)) [NeZero n], GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → (∀ (r : PtY ST SG Q y) (p : DecoF X.E n ST SG Q), ∃ r' : PtY ST SG Q y, r'.1.1 = p ∧ bar r' = bar r ∧ cq r' = cq r) → (∀ b r r', bar r = bar r' → cq r = cq r' → bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = bar (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r')) ∧ cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r)) = cq (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl b r'))) → ∀ (c₀ : (stR Λ Θ p₀ pref).Cl) (p : (stR Λ Θ p₀ pref).Cl → Prop), (∀ c, p c ↔ c.1 = c₀.1 ∧ bar (rp Λ Θ p₀ pref c) = bar (rp Λ Θ p₀ pref c₀) ∧ cq (rp Λ Θ p₀ pref c) = cq (rp Λ Θ p₀ pref c₀)) → Function.Bijective fun c : {c // p c} => (Quotient.mk'' (rp Λ Θ p₀ pref c.1).1.1 : DecoFCl (K := X.K) n ST SG Q (chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀))) (GlobalTheory.Mem.Col2.ChEx.cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀)))) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq _ hact hdet hsur hnorm c₀ p hp
  constructor
  · rintro ⟨c, h⟩ ⟨c', h'⟩ e
    obtain ⟨h1, h2, h3⟩ := (hp c).1 h
    obtain ⟨h1', h2', h3'⟩ := (hp c').1 h'
    apply Subtype.ext
    show c = c'
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact' e)
    have hb : bar (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = bar (rp Λ Θ p₀ pref c') :=
      (bar_ya_eq_iff _ _ _ _).2 fun w => by rw [h2']; exact (mem_chG.1 g.2.1.2).2 w
    have hq : cq (ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')) = cq (rp Λ Θ p₀ pref c') := by
      funext P
      rw [hact, h3']
      exact (image_eq_iff_frStab _ _).2 ((mem_cutQ_grp.1 g.2.2.2).2 P)
    have e2 : ya (Λ c₀.1) (Θ c₀.1) (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c') = rp Λ Θ p₀ pref c :=
      hdet _ _ (by rw [ya_frLift]; exact hg) (hb.trans (h2'.trans h2.symm)) (hq.trans (h3'.trans h3.symm))
    have e3 := cl_ya Λ Θ p₀ pref c₀.1 (frLift _ _ _ _ g) (rp Λ Θ p₀ pref c')
    rw [e2] at e3
    have e4 := cl_rp Λ Θ p₀ pref c
    have e5 := cl_rp Λ Θ p₀ pref c'
    have t : ∀ b b' : β, b = b' → ∀ q : PtY ST SG Q y, (stR Λ Θ p₀ pref).cl b q = (stR Λ Θ p₀ pref).cl b' q := by
      rintro b _ rfl q
      rfl
    exact e4.symm.trans ((t _ _ h1 _).trans (e3.trans ((t _ _ h1' _).symm.trans e5)))
  · intro z
    induction z using Quotient.inductionOn' with
    | h d =>
      obtain ⟨r', h1, h2, h3⟩ := hsur (rp Λ Θ p₀ pref c₀) d
      obtain ⟨hb, hq⟩ := hnorm c₀.1 _ _ h2.symm h3.symm
      rw [cl_rp] at hb hq
      refine ⟨⟨(stR Λ Θ p₀ pref).cl c₀.1 r', (hp _).2 ⟨rfl, hb.symm, hq.symm⟩⟩, ?_⟩
      obtain ⟨g, hg⟩ := exists_ya Λ Θ p₀ pref c₀.1 r'
      rw [hg] at hb hq
      have hb' : bar (ya (Λ c₀.1) (Θ c₀.1) g r') = bar r' := hb.symm.trans h2.symm
      have hq' : cq (ya (Λ c₀.1) (Θ c₀.1) g r') = cq r' := hq.symm.trans h3.symm
      rw [bar_ya_eq_iff, h2] at hb'
      have hC : ∀ P : Q, g.2.2.1 P ∈ frStab P.1 (cq (rp Λ Θ p₀ pref c₀) P) := fun P => by
        rw [← h3, ← image_eq_iff_frStab]
        have := congrFun hq' P
        rwa [hact] at this
      let g' : UF X.E n × chG (Λ c₀.1) (bar (rp Λ Θ p₀ pref c₀)) × (cutQ (Θ c₀.1) (cq (rp Λ Θ p₀ pref c₀))).grp :=
        (g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, hb'⟩⟩, ⟨g.2.2.1, mem_cutQ_grp.2 ⟨g.2.2.2, hC⟩⟩)
      refine Quotient.sound' (MulAction.orbitRel_apply.2 ⟨g', ?_⟩)
      show g' • d = (rp Λ Θ p₀ pref ((stR Λ Θ p₀ pref).cl c₀.1 r')).1.1
      rw [hg, ← h1]
      rfl

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetMovesWithFrameChange
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in
theorem frsF_ya_symm {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)) (hP : P.1 ∉ Pr.vGs) (y : Sp X.E (R.N j)) :
    (frsF sel mu (ya Λ Θ g r).1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm (g.1.1 y) =
      (g.2.2.1 P).1 ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y) := by
  rw [LinearEquiv.symm_apply_eq]
  have e1 : (⟨P.1, (Finset.mem_union.mp (Finset.mem_union_right _ P.2)).resolve_left hP⟩ : QE sel (mu : Chr X.F X.E X.K)) = P :=
    Subtype.ext rfl
  simp only [frsF, dif_neg hP, e1]
  show _ = (g.1.1 * r.1.1.1.2 P * ((g.2.2.1 P)⁻¹).1) ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y))
  have e2 : ((g.2.2.1 P)⁻¹).1 ((g.2.2.1 P).1 ((r.1.1.1.2 P).symm y)) = (r.1.1.1.2 P).symm y := by
    show (g.2.2.1 P).1.symm ((g.2.2.1 P).1 _) = _
    exact LinearEquiv.symm_apply_apply _ _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e2]
  show g.1.1 y = g.1.1 ((r.1.1.1.2 P) ((r.1.1.1.2 P).symm y))
  rw [LinearEquiv.apply_symm_apply]

theorem invActs_cqOf : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → GlobalTheory.Mem.Col2.ChEx.InvActs (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  intro X Pr R sel S mu cst u j hQ Λ Θ g r P
  have hP := hQ P.1 P.2
  ext z
  simp only [cqOf, cosetIn, Set.mem_setOf_eq, Set.mem_image, if_neg hP]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨(g.2.2.1 P).1.symm z, ⟨y, hy, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    rw [frsF_ya_symm Λ Θ g r P hP y] at hz
    rw [← (g.2.2.1 P).2]
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨z0, ⟨y, hy, hz⟩, rfl⟩
    refine ⟨g.1.1 y, ⟨y, hy, rfl⟩, ?_⟩
    rw [frsF_ya_symm Λ Θ g r P hP y, ← map_sub, ← map_smul]
    exact ((g.2.2.1 P).2 _).2 hz

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLevelFormsIffStdGroupTypeSpaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLevelForms_iff_stdGroupTypeSpace : ∀ (D : D7) (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E)) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (c : CoefA V) (P : principalLevelFrame.RowPsi V V.rank) (e : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V), V.gram = 1 → UnitFr P → RatIso P e → ∀ (G₀ : Type) [Group G₀] (red : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q →* G₀) (eG : G₀ ≃* G0 Pg D.R.r) (P₀ : Subgroup G₀) (ψ₀ : P₀ →* D.what₂.LLˣ), (∀ q : (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q, eG (red q) = rTup 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))) → ∀ F : Bridge.Gf V → c.W, F ∈ cutSp (Bridge.ratF V) c.coef.ρ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).J (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).χ (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).Q (levEnv V 1 (datV D V.rank hr Pg Q (LevelP.triv _ _ _) chi xi)).ch red P₀ ((Units.map D.what₂.embLL.toMonoidHom).comp ψ₀⁻¹) ↔ (fun g => F (toGf P g)) ∈ NG.TypeSp (wtRep c e) (stdJ (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) (stdX (datV D V.rank hr Pg Q (levPOf eG D.what₂.embLL P₀ ψ₀) chi xi)) := by
  first | exact @GlobalTheory.MtInType.cutSp_iff_typeSp | exact GlobalTheory.MtInType.cutSp_iff_typeSp | (intros; apply GlobalTheory.MtInType.cutSp_iff_typeSp <;> assumption)
end

