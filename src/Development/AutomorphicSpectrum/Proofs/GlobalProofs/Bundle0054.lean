module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchMatBlockEmbInfGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisBlockEntries
section
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

open GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.CompanionTheory.BlockEntry

theorem sandwich_single_apply {A B : Type} [Fintype A] {d : ℕ} (U : Matrix A (Fin d) ℂ) (W : Matrix (Fin d) B ℂ)
    (i j : Fin d) (z : ℂ) (a : A) (c : B) : (U * Matrix.single i j z * W) a c = U a i * z * W j c := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_and]

theorem rows_of_adapted {n m : ℕ} {H P : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin m) ℂ}
    (hxx : Xᴴ * H * X = 0) (hyy : Yᴴ * H * Y = 0) (hxy : Xᴴ * H * Y = 1) (hyx : Yᴴ * H * X = 1) (hle : 2 * m ≤ n)
    (cX : ∀ (c : Fin n) (k : Fin m), c.val = k.val → ∀ a, P a c = X a k)
    (cY : ∀ (c : Fin n) (k : Fin m), c.val + k.val + 1 = n → ∀ a, P a c = Y a k)
    (pX : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Xᴴ * H * P) k c = 0)
    (pY : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Yᴴ * H * P) k c = 0) (k : Fin m) (c : Fin n) :
    (Yᴴ * H * P) k c = (if c.val = k.val then 1 else 0) ∧
      (Xᴴ * H * P) k c = (if c.val + k.val + 1 = n then 1 else 0) := by
  have hk := k.2
  have hc := c.2
  by_cases h1 : c.val < m
  · have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * X) k ⟨c.val, h1⟩ := fun M => by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [cX c ⟨c.val, h1⟩ rfl a]
    rw [e, e, hyx, hxx, Matrix.one_apply, Matrix.zero_apply]
    refine ⟨?_, ?_⟩
    · by_cases e' : c.val = k.val
      · rw [if_pos e', if_pos (Fin.ext e'.symm)]
      · rw [if_neg e', if_neg fun e'' => e' (congrArg Fin.val e'').symm]
    · rw [if_neg (by omega)]
  · by_cases h2 : c.val + m < n
    · rw [pX c (by omega) h2, pY c (by omega) h2, if_neg (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    · have hk' : n - 1 - c.val < m := by omega
      have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * Y) k ⟨n - 1 - c.val, hk'⟩ := fun M => by
        simp only [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun a _ => by rw [cY c ⟨n - 1 - c.val, hk'⟩ (by simp only; omega) a]
      rw [e, e, hyy, hxy, Matrix.one_apply, Matrix.zero_apply]
      refine ⟨by rw [if_neg (by omega)], ?_⟩
      by_cases e' : c.val + k.val + 1 = n
      · rw [if_pos e', if_pos (Fin.ext (by simp only; omega))]
      · rw [if_neg e', if_neg fun e'' => e' (by have := congrArg Fin.val e''; simp only at this; omega)]

theorem conj_units_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) {m : ℕ}
    {X Y : Matrix (Fin n) (Fin m) E} (hW : IsWittFrame σ J X Y) {l d : ℕ} (h : l + d ≤ m) {C : GL (Fin n) E}
    (hC : GlobalTheory.BlockForms.IsAdapted σ J X Y C) (τ : E →+* ℂ) (i j : Fin d) (p q p' q' : Fin n)
    (hp : p.val = l + i.val) (hq : q.val = l + j.val) (hp' : p'.val + l + j.val + 1 = n)
    (hq' : q'.val + l + i.val + 1 = n) (z : ℂ) :
    z • (C.1.map τ * Matrix.single p q 1 * (C.1.map τ)⁻¹) -
        (starRingEnd ℂ z) • (C.1.map τ * Matrix.single p' q' 1 * (C.1.map τ)⁻¹) =
      (GlobalTheory.BlockForms.blkCols h X).map τ * Matrix.single i j z * (((GlobalTheory.BlockForms.blkCols h Y).map τ)ᴴ * J.map τ) -
        (GlobalTheory.BlockForms.blkCols h Y).map τ * (Matrix.single i j z)ᴴ * (((GlobalTheory.BlockForms.blkCols h X).map τ)ᴴ * J.map τ) := by
  classical
  set P := C.1.map τ with hP
  have hdet : IsUnit P.det := by
    have e : P.det = τ C.1.det := by rw [hP, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 C.isUnit).map τ
  obtain ⟨hxx, hyy, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW τ
  have hJh : (J.map τ)ᴴ = J.map τ := GlobalTheory.LeviHC.conjTranspose_map hcm hJ τ
  have hyx := GlobalTheory.CentreFin.dual_swap hJh hxy
  have perp : ∀ (A : Matrix (Fin n) (Fin m) E) (c : Fin n), (Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c) = 0 →
      ∀ k, ((A.map τ)ᴴ * J.map τ * P) k c = 0 := fun A c e k => by
    have e1 : ((Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c)) k = 0 := by rw [e]; rfl
    have e2 := congrArg τ e1
    rw [map_zero] at e2
    rw [← e2, ← GlobalTheory.CentreFin.map_cT_emb hcm τ A, ← Matrix.map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP, map_sum, map_mul]
  have what₂ := rows_of_adapted (P := P) hxx hyy hxy hyx hC.le
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.colX c k e a, Matrix.map_apply])
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.columnBlock c k e a, Matrix.map_apply])
    (fun c h1 h2 => perp X c (hC.perpX c h1 h2)) (fun c h1 h2 => perp Y c (hC.perpY c h1 h2))
  set Xb := (GlobalTheory.BlockForms.blkCols h X).map τ with hXb
  set Yb := (GlobalTheory.BlockForms.blkCols h Y).map τ with hYb
  set R := Xb * Matrix.single i j z * (Ybᴴ * J.map τ) - Yb * (Matrix.single i j z)ᴴ * (Xbᴴ * J.map τ) with hR
  let f : Fin d → Fin m := fun a => ⟨l + a.val, by omega⟩
  have sY : ∀ (a : Fin d) (c : Fin n), (Ybᴴ * J.map τ * P) a c = if c.val = l + a.val then 1 else 0 := fun a c =>
    (what₂ (f a) c).1
  have sX : ∀ (a : Fin d) (c : Fin n), (Xbᴴ * J.map τ * P) a c = if c.val + (l + a.val) + 1 = n then 1 else 0 := fun a c =>
    (what₂ (f a) c).2
  have hRP : R * P = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) := by
    ext a c
    have e1 : R * P = Xb * Matrix.single i j z * (Ybᴴ * J.map τ * P) -
        Yb * Matrix.single j i (starRingEnd ℂ z) * (Xbᴴ * J.map τ * P) := by
      rw [hR, Matrix.sub_mul, Matrix.conjTranspose_single]
      simp only [Matrix.mul_assoc]
      rfl
    have e2 : P a p = Xb a i := by
      rw [hP, Matrix.map_apply, hC.colX p (f i) hp a]; rfl
    have e3 : P a p' = Yb a j := by
      rw [hP, Matrix.map_apply, hC.columnBlock p' (f j) (by simp only [f]; omega) a]; rfl
    rw [e1, Matrix.sub_apply, sandwich_single_apply, sandwich_single_apply, sY, sX, Matrix.mul_sub, Matrix.sub_apply,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply]
    have e4 : ∀ (u v : Fin n), (P * Matrix.single u v (1 : ℂ)) a c = P a u * (if c = v then 1 else 0) := fun u v => by
      by_cases e : c = v
      · subst e
        simp [Matrix.mul_single_apply_same]
      · have e' : v ≠ c := fun e'' => e e''.symm
        rw [if_neg e, mul_zero, Matrix.mul_apply]
        exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_apply_of_col_ne _ _ e' _, mul_zero]
    rw [e4, e4, e2, e3]
    have c1 : (c = q) ↔ c.val = l + j.val := by rw [Fin.ext_iff, hq]
    have c2 : (c = q') ↔ c.val + (l + i.val) + 1 = n := by rw [Fin.ext_iff]; omega
    simp only [c1, c2, smul_eq_mul]
    ring
  calc _ = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) * P⁻¹ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = R := by rw [← hRP, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]

theorem lieS_eq_derEnd : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : GlobalTheory.CuspRep.Sm D.host.E d), (∀ x, f.1 x = F.1 (ι x)) →
    ∀ (i j : Fin d) (p q p' q' : Fin V.rank), p.val = l + i.val → q.val = l + j.val →
    p'.val + l + j.val + 1 = V.rank → q'.val + l + i.val + 1 = V.rank → ∀ (z : ℂ) (x : GlobalTheory.CuspRep.GA D.host.E d),
      (GlobalTheory.CuspRep.lieS D.host.E d i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) f).1 x =
        (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
          (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) F).1 (ι x) := by
  intro D _ θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' hp hq hp' hq' z x
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  obtain ⟨e, he⟩ : ∃ e : EmbOver D.host.E (placeOf D τ), e.1 = tauE D τ := ⟨embOverOf D τ, rfl⟩
  have hline := isLineOf_blockEmb_exp' _ D.host.E D.sp.cm.sig hcm V.rank V.gram hJ m X Y hW l d h ι hι (placeOf D τ)
    e (Matrix.single i j z)
  have hmat := conj_units_eq hcm hJ hW h hC (tauE D τ) i j p q p' q' hp hq hp' hq' z
  rw [he, ← hmat] at hline
  have hsk := hline.skew hcm
  rw [he] at hsk
  have hZ : z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
      (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹) ∈ lieAt V τ := hsk
  have hγ : ∀ t : ℝ, ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t • (Matrix.single i j z).map
      (GlobalTheory.CuspRep.atEmb (tauE D τ))))) = oneP θ V τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
        (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) t := fun t => by
    obtain ⟨y, e1, e2⟩ := hline t
    refine Eq.trans e1 ?_
    rw [oneP, ← e2, GlobalTheory.Orb.archMat_eq_archEquiv _ hcm, atTau_archEquiv hθ V e he]
  have h0 : GlobalTheory.CuspRep.atEmb (tauE D τ) 0 = 0 := by rw [GlobalTheory.CuspRep.atEmb_eq]; simp
  have hs : Matrix.single i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) = (Matrix.single i j z).map (GlobalTheory.CuspRep.atEmb (tauE D τ)) := by
    ext a b; simp only [Matrix.single_apply, Matrix.map_apply]; split_ifs <;> simp [h0]
  rw [GlobalTheory.CuspRep.lieS_apply, hs, lie_eq_deriv_exp' D.host.E d f _ x]
  change _ = RderC θ V τ _ F.1 (ι x)
  rw [GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hZ]
  simp only [hf, map_mul, hγ]
  rfl

end GlobalTheory.CompanionTheory.BlockEntry
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterTrivialAlmostEverywhere
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

section FoundMeas
open GroundTheory.Global
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing GroundTheory.Global.measurableSpace_infiniteAdeleRing

variable (F : Type) [Field F] [NumberField F]

abbrev ratA : AddSubgroup (AF F) := (algebraMap F (AF F)).toAddMonoidHom.range

theorem isFD_fundamentalSet (ν : Measure (AdeleRing (𝓞 F) F)) :
    IsAddFundamentalDomain (ratA F) (fundamentalSet F) ν := by
  refine IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet F).nullMeasurableSet fun x ↦ ?_
  obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_fundamentalSet F x
  refine ⟨⟨algebraMap F (AF F) (-k), -k, rfl⟩, ?_, ?_⟩
  · change algebraMap F (AF F) (-k) + x ∈ fundamentalSet F
    rwa [map_neg, neg_add_eq_sub]
  · rintro ⟨_, k', rfl⟩ h
    change algebraMap F (AF F) k' + x ∈ fundamentalSet F at h
    have hk' : -k' = k := huniq (-k') (by
      change x - algebraMap F (AF F) (-k') ∈ fundamentalSet F
      rwa [map_neg, sub_neg_eq_add, add_comm])
    refine Subtype.ext ?_
    change algebraMap F (AF F) k' = algebraMap F (AF F) (-k)
    rw [← hk', neg_neg]

variable {F}

theorem eq_adeleMeasure (db : Measure (AdeleRing (𝓞 F) F)) (hH : db.IsAddHaarMeasure) (D : Set (AF F))
    (hD : IsAddFundamentalDomain (ratA F) D db) (hD1 : db D = 1) : db = adeleMeasure F := by
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := countable_numberField F
  haveI : Countable (ratA F) := (AddMonoidHom.rangeRestrict_surjective _).countable
  have hl : db = Measure.addHaarScalarFactor db (adeleMeasure F) • adeleMeasure F :=
    Measure.isAddLeftInvariant_eq_smul db (adeleMeasure F)
  have h2 : db (fundamentalSet F) = 1 := ((isFD_fundamentalSet F db).measure_eq hD).trans hD1
  rw [hl, Measure.smul_apply, adeleMeasure_fundamentalSet] at h2
  have hc : Measure.addHaarScalarFactor db (adeleMeasure F) = 1 := by
    simpa [ENNReal.smul_def] using h2
  rw [hl, hc, one_smul]

theorem covol_transfer (db : @Measure (AF F) measAF) (hdb : IsCovolOne db)
    [m : MeasurableSpace (AF F)] (hm : m = measAF) :
    ∃ μ : Measure (AF F), (∀ s, μ s = db s) ∧ μ.IsAddHaarMeasure ∧
      ∃ D : Set (AF F), IsAddFundamentalDomain (ratA F) D μ ∧ μ D = 1 := by
  subst hm
  obtain ⟨h1, D, h2, h3⟩ := hdb
  exact ⟨db, fun _ => rfl, h1, D, h2, h3⟩

end FoundMeas

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM

theorem prod_congr_inf {F : Type} [Field F] [NumberField F] {m₁ m₂ : MeasurableSpace (Ainf F)} (h : m₁ = m₂)
    (l₁ : @Measure (Ainf F) m₁) (l₂ : @Measure (Ainf F) m₂) (hl : ∀ s, l₁ s = l₂ s) (lf : Measure (Af F))
    (s : Set (Ainf F × Af F)) :
    @Measure.prod (Ainf F) (Af F) m₁ _ l₁ lf s = @Measure.prod (Ainf F) (Af F) m₂ _ l₂ lf s := by
  subst h
  obtain rfl : l₁ = l₂ := Measure.ext fun s _ => hl s
  rfl

theorem prod_meas_eq (F : Type) [Field F] [NumberField F] :
    (inferInstance : MeasurableSpace (Ainf F × Af F)) = (measAF : MeasurableSpace (AF F)) := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  exact (Prod.borelSpace (α := Ainf F) (β := Af F)).measurable_eq

def pairE (F : Type) [Field F] [NumberField F] : (Ainf F × Af F) ≃ᵐ AF F where
  toEquiv := Equiv.refl _
  measurable_toFun := by
    intro s hs
    rw [← prod_meas_eq F] at hs
    exact hs
  measurable_invFun := by
    intro s hs
    have hs' : @MeasurableSet (AF F) measAF s := by
      rw [← prod_meas_eq F]
      exact hs
    exact hs'

theorem prodM : ∀ (F : Type) [Field F] [NumberField F] (db : Measure (AF F)), IsCovolOne db → ∀ laminf : Measure (Ainf F), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 ∧ ∃ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) ∧ MeasurePreserving e (laminf.prod lf) db := by
  intro F _ _ db hdb laminf hinf
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  refine ⟨lf, hlf, h1, pairE F, fun p => rfl, (pairE F).measurable, ?_⟩
  have hA : GroundTheory.Global.measurableSpace_adeleRing F = (measAF : MeasurableSpace (AF F)) :=
    (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq
  have hI : GroundTheory.Global.measurableSpace_infiniteAdeleRing F = (measAinf : MeasurableSpace (Ainf F)) :=
    (GroundTheory.Global.borelSpace_infiniteAdeleRing F).measurable_eq
  obtain ⟨μ, hμ, hH, D, hD, hD1⟩ :=
    @covol_transfer F _ _ db hdb (GroundTheory.Global.measurableSpace_adeleRing F) hA
  obtain ⟨l, hl, hlH, E, hE, hE1⟩ :=
    @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.std_transfer F _ _ laminf hinf (GroundTheory.Global.measurableSpace_infiniteAdeleRing F) hI
  have h2 := eq_adeleMeasure μ hH D hD hD1
  have h3 := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.adele_eq l hlH E hE hE1 lf hlf h1
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (pairE F).measurable hs]
  have e1 : (pairE F) ⁻¹' s = s := rfl
  rw [e1, ← prod_congr_inf hI l laminf hl lf s, ← hμ s]
  have e2 := congrArg (fun ν => ν s) h3
  have e3 := congrArg (fun ν => ν s) h2
  exact e2.trans e3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.ProdM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FrameFamilyRightTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

theorem foldr_lineDer_mul_right {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GAd σ J) (l : List (ℝ → GAd σ J))
    (f : GAd σ J → ℂ) :
    l.foldr lineDer (fun x => f (x * b)) =
      fun x => (l.map fun γ t => b⁻¹ * γ t * b).foldr lineDer f (x * b) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.foldr_cons]
    funext x
    simp only [lineDer]
    congr 1
    funext t
    congr 1
    simp only [mul_assoc, mul_inv_cancel_left]

variable {D : D7}

theorem isSmModOn_mul_right (V : HSp D) {Γ : Set (GA D V)} {φ : GA D V → ℂ}
    (h : IsSmModOn D.sp.cm.sig V.gram Γ φ) (b : GA D V) :
    IsSmModOn D.sp.cm.sig V.gram Γ (fun x => φ (x * b)) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hN : (GfC V).Normal := MonoidHom.normal_ker _
  refine ⟨fun γ hγ x => ?_, ?_, h.cont.comp (continuous_id.mul continuous_const), ?_, ?_⟩
  · show φ (γ * x * b) = φ (x * b)
    rw [mul_assoc]
    exact h.left γ hγ _
  · obtain ⟨A, hA, eA⟩ := h.level
    refine ⟨A.comap (MulAut.conj b⁻¹).toMonoidHom, ?_, fun k hk hk' x => ?_⟩
    · have hc : Continuous fun y : GA D V => b⁻¹ * y * b⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hA.preimage hc
    · have hk2 : b⁻¹ * k * b⁻¹⁻¹ ∈ A := hk
      have hk3 : b⁻¹ * k * b⁻¹⁻¹ ∈ GfC V := hN.conj_mem k hk' b⁻¹
      rw [inv_inv] at hk2 hk3
      show φ (x * k * b) = φ (x * b)
      rw [← eA _ hk2 hk3 (x * b)]
      congr 1
      simp only [mul_assoc, mul_inv_cancel_left]
  · exact GlobalTheory.UAut.isSm_mul_right_of_isCMExt _ _ (GlobalTheory.AdelicU.isCMExt_host D) φ b h.smooth
  · obtain ⟨N, hN'⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN' (l.map fun γ t => b⁻¹ * γ t * b) (by
      intro γ' hγ'
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hγ'
      exact GlobalTheory.UAut.RightTranslate.isRealLine_conj (GlobalTheory.AdelicU.isCMExt_host D) (hl γ hγ) b)
    refine ⟨max C 0 * (height D.sp.cm.sig V.gram b : ℝ) ^ N, fun x => ?_⟩
    rw [foldr_lineDer_mul_right]
    have h1 : (height D.sp.cm.sig V.gram (x * b) : ℝ) ≤
        (height D.sp.cm.sig V.gram x : ℝ) * (height D.sp.cm.sig V.gram b : ℝ) := by
      exact_mod_cast height_mul_le _ _ x b
    have h0 : (0 : ℝ) ≤ (height D.sp.cm.sig V.gram (x * b) : ℝ) := by positivity
    calc ‖(l.map fun γ t => b⁻¹ * γ t * b).foldr lineDer φ (x * b)‖
        ≤ C * (height D.sp.cm.sig V.gram (x * b) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height D.sp.cm.sig V.gram (x * b) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height D.sp.cm.sig V.gram x : ℝ) * (height D.sp.cm.sig V.gram b : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 N) (le_max_right _ _)
      _ = max C 0 * (height D.sp.cm.sig V.gram b : ℝ) ^ N * (height D.sp.cm.sig V.gram x : ℝ) ^ N := by
          rw [mul_pow]; ring

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem infMat_inv_mul (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) :
    infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) b = 1 ∧
      infMat D.sp.cm.sig V.gram (θ τ) b * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ = 1 := by
  have rp := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hm := rp.2.2.2.1
  have h1 : infMat D.sp.cm.sig V.gram (θ τ) 1 = 1 := rp.2.2.2.2.1 1 (one_mem _) τ
  exact ⟨by rw [← hm, inv_mul_cancel, h1], by rw [← hm, mul_inv_cancel, h1]⟩

theorem isFrame_mul_inv (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ) :
    IsUnit (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ∧
      (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)ᴴ * Formalism.REAL.Jm e * (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) =
        gramAt D V τ := by
  obtain ⟨e1, e2⟩ := infMat_inv_mul hθ V b τ
  rw [Matrix.inv_eq_left_inv e1]
  have hB : IsUnit (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹) := ⟨⟨_, _, e1, e2⟩, rfl⟩
  refine ⟨hP.mul hB, ?_⟩
  have hu : (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹)ᴴ * gramAt D V τ * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ =
      gramAt D V τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V b⁻¹ τ
  rw [← hu, ← h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem inv_mul_kAt_mul (hθ : IsInfFam θ) (V : HSp D) (b : GA D V) (τ : D.what₂.Tau) {e : Fin V.rank → Bool}
    {P : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm e * P = gramAt D V τ)
    (k : Formalism.REAL.KG e) :
    b⁻¹ * kAt θ V τ e (P * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b = kAt θ V τ e P k := by
  obtain ⟨hP', h'⟩ := isFrame_mul_inv hθ V b τ hP h
  have hx := isAtTau_kAt θ V hθ τ hP' h' k
  have rp := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hm := rp.2.2.2.1
  have hN : (GinfC V).Normal := MonoidHom.normal_ker _
  refine Model.isAtTau_unique θ V hθ ⟨?_, ?_, fun τ' c => ?_⟩ (isAtTau_kAt θ V hθ τ hP h k)
  · have := hN.conj_mem _ hx.1 b⁻¹
    rwa [inv_inv] at this
  · obtain ⟨e1, e2⟩ := infMat_inv_mul hθ V b τ
    rw [hm, hm, hx.2.1, Matrix.inv_eq_left_inv e1, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv e2]
    simp only [Matrix.mul_assoc]
    rw [e1, Matrix.mul_one, ← Matrix.mul_assoc (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹), e1, Matrix.one_mul]
  · obtain ⟨e1, -⟩ := infMat_inv_mul hθ V b τ'
    rw [hm, hm, hx.2.2 _ c, Matrix.mul_one, e1]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl

theorem cuspOn_mul_right : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (φ : GA D V → ℂ), φ ∈ cuspOn θ V X Y T U ε fr ρ c → ∀ b : GA D V, (fun x => φ (x * b)) ∈ cuspOn θ V X Y T (U.map (MulAut.conj b).toMonoidHom) ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) ρ c := by
  intro D θ hθ V U ε fr hfr W _ _ ρ c m X Y T φ hφ b
  obtain ⟨⟨f1, f2, f3, f4⟩, f5⟩ := hφ
  have hN : (GfC V).Normal := MonoidHom.normal_ker _
  refine ⟨⟨isSmModOn_mul_right V f1 b, fun u hu hu' g => ?_, fun τ x => ?_, fun τ k => ?_⟩, fun T' hT' => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hu' ⊢
    have ha' : a ∈ GfC V := by
      have := hN.conj_mem _ hu' b⁻¹
      simpa [mul_assoc] using this
    rw [← f2 a ha ha' (g * b)]
    congr 1
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · have e : (fun k => φ (x * kAt θ V τ (ε τ) (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b)) =
        fun k => φ (x * b * kAt θ V τ (ε τ) (fr τ) k) := funext fun k => by
      rw [← inv_mul_kAt_mul hθ V b τ (hfr τ).1 (hfr τ).2 k]
      simp only [mul_assoc, mul_inv_cancel_left]
    show (fun k => φ (x * kAt θ V τ (ε τ) (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) k * b)) ∈ coeffSpan (ρ τ)
    rw [e]
    exact f3 τ (x * b)
  · have := GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ b τ k (GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ f1.smooth)
    show gelf θ V τ k (rTr V b φ) = c τ k • rTr V b φ
    rw [this, f4]
    rfl
  · intro μ 𝓕 hμ h𝓕 h1 g
    have := f5 T' hT' μ 𝓕 hμ h𝓕 h1 (g * b)
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

theorem isFrameFam_mul_infMat_inv : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsFrameFam V ε fr → ∀ b : GA D V,
        IsFrameFam V ε (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) := by
  intro D θ hθ V ε fr h b τ
  have h1 : infMat D.sp.cm.sig V.gram (θ τ) b * infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, mul_inv_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have h2 : infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ * infMat D.sp.cm.sig V.gram (θ τ) b = 1 := by
    rw [← Formalism.L2.Fam.ThC.infMat_mul, inv_mul_cancel, Formalism.L2.Fam.ThC.infMat_one]
  have hu : IsUnit (infMat D.sp.cm.sig V.gram (θ τ) b⁻¹) := IsUnit.of_mul_eq_one _ h2
  have hinv : (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹ = infMat D.sp.cm.sig V.gram (θ τ) b⁻¹ :=
    Matrix.inv_eq_right_inv h1
  refine ⟨?_, ?_⟩
  · show IsUnit (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)
    rw [hinv]
    exact (h τ).1.mul hu
  · show (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹)ᴴ * Formalism.REAL.Jm (ε τ) *
        (fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b)⁻¹) = _
    rw [hinv, Matrix.conjTranspose_mul]
    have e := GlobalTheory.Doubling.infMat_isometry (V := V) hθ τ b⁻¹
    rw [← (h τ).2] at e ⊢
    simpa only [Matrix.mul_assoc] using e

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

