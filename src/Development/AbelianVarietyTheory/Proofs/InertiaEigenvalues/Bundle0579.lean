module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LineOfSingleJump
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositive
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
  GlobalTheory.NormCompat

namespace GlobalTheory.ProdLocUnitPos

theorem prod_locUnit_eq_one_of_pos : ∀ (F : Type) [Field F] [NumberField F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → (∀ y ∈ GlobalTheory.HeckeGal.infConn F, ψ y = 1) → ∀ a : Fˣ, (∀ φ : F →+* ℝ, 0 < φ (a : F)) → ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (∀ v ∉ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1) → ∏ v ∈ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1 := by
  intro F _ _ B _ ψ hker hd hconn a ha T hT
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ hker
  let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let P : Ideles F →* (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let u : (InfiniteAdeleRing F)ˣ := P (diagUnits F a)
  have hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing F)ˣ :=
    GlobalTheory.RayFromArtin.mem_connectedComponentOfOne_of_pos a ha
  have hinf : ψ (ι u) = 1 := hconn _ ⟨u, hu, rfl⟩
  let av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ :=
    fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let z : Ideles F := diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹
  have hPι : P (ι u) = u := Units.ext rfl
  have hPl : ∀ v, P (locUnit F v a) = 1 := fun v => Units.ext rfl
  have hz1 : (z : AdeleRing (𝓞 F) F).1 = 1 := by
    have h : P z = 1 := by
      simp only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]
      exact mul_inv_cancel u
    exact congrArg Units.val h
  have hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (diagUnits F a) = av v := fun v => Units.ext rfl
  have hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1 := fun v => Units.ext rfl
  have hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1 := by
    intro v w
    apply Units.ext
    split_ifs with h
    · subst h
      exact GlobalTheory.Mem.LocTriv.ev_local_self w _
    · exact GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _
  have hzl : ∀ v, ψ (localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1 := by
    intro v
    have e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹ := by
      simp only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]
    rw [e, Finset.prod_ite_eq' T v]
    split_ifs with hv
    · rw [mul_inv_cancel, map_one, map_one]
    · rw [inv_one, mul_one]
      exact hT v hv
  have hz := GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl
  simp only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz
  exact inv_eq_one.mp hz

end GlobalTheory.ProdLocUnitPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.GalD

theorem smul_cancel {R : Type} [CommRing R] {m n : Type} {c : R} (hc : c ∈ nonZeroDivisors R)
    {M M' : Matrix m n R} (h : c • M = c • M') : M = M' := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 h1

theorem map_smul_hom {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem mul_eq_smul_comm {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    {X X' : Matrix n n R} {c : R} (hc : c ∈ nonZeroDivisors R) (h : X * X' = c • (1 : Matrix n n R)) :
    X' * X = c • (1 : Matrix n n R) := by
  have hdet : X.det ∈ nonZeroDivisors R := by
    have h4 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    have h5 : X.det * X'.det ∈ nonZeroDivisors R := h4 ▸ pow_mem hc _
    exact (mul_mem_nonZeroDivisors.1 h5).1
  have h2 : X * (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one,
      sub_self]
  have h3 : X.det • (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [← Matrix.one_mul (X' * X - c • (1 : Matrix n n R)), ← smul_mul_assoc, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h2, Matrix.mul_zero]
  rw [← smul_zero X.det] at h3
  exact sub_eq_zero.1 (smul_cancel hdet h3)

theorem key {R : Type} [CommRing R] {n : Type} [Fintype n] {P YG Ya U UG Bi Bg ε : Matrix n n R}
    {L e ge t gt : R} {N : ℕ} (hc : L * ge ^ (2 * N) * e ^ (2 * N) ∈ nonZeroDivisors R)
    (hY : U * Bi = (L * e ^ (2 * N)) • Ya) (hYG : UG * Bg = (L * ge ^ (2 * N)) • YG)
    (hgal : (e * t) ^ N • (P * UG) = (ge * gt) ^ N • U) (hR : ge ^ N • (Bi * ε) = e ^ N • Bg) :
    t ^ N • (P * YG) = gt ^ N • (Ya * ε) := by
  refine smul_cancel hc ?_
  calc (L * ge ^ (2 * N) * e ^ (2 * N)) • (t ^ N • (P * YG))
      = (e ^ N * (e * t) ^ N) • (P * ((L * ge ^ (2 * N)) • YG)) := by
        rw [smul_smul, mul_smul_comm, smul_smul]; congr 1; ring
    _ = (e ^ N * (e * t) ^ N) • (P * (UG * Bg)) := by rw [hYG]
    _ = e ^ N • (((e * t) ^ N • (P * UG)) * Bg) := by rw [smul_mul_assoc, Matrix.mul_assoc, smul_smul]
    _ = e ^ N • (((ge * gt) ^ N • U) * Bg) := by rw [hgal]
    _ = (ge * gt) ^ N • (U * (e ^ N • Bg)) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, mul_comm]
    _ = (ge * gt) ^ N • (U * (ge ^ N • (Bi * ε))) := by rw [hR]
    _ = ((ge * gt) ^ N * ge ^ N) • ((U * Bi) * ε) := by rw [mul_smul_comm, smul_smul, Matrix.mul_assoc]
    _ = ((ge * gt) ^ N * ge ^ N) • (((L * e ^ (2 * N)) • Ya) * ε) := by rw [hY]
    _ = (L * ge ^ (2 * N) * e ^ (2 * N)) • (gt ^ N • (Ya * ε)) := by
        rw [smul_mul_assoc, smul_smul, smul_smul]; congr 1; ring

end GlobalTheory.BSP.GalD


open GlobalTheory.BSP.GalD in
theorem GlobalTheory.BSP.Height.rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  intro l _ K bk d ρ τ s ht _hτ g ε hrel
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := NNReal.rpow_pos hl0
  have h0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  have h1 : ‖toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).1
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev h0 with hi_def
  set G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (Per.σA (g : GQ l)) h1 with hG_def
  have hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i := isDiscMap_map _ _
  have hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G := isDiscMap_map _ _
  have hFg : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf ((ainfHom K g).comp bk.ι)) (G.comp i) :=
    ⟨fun a => by
      change G (i (toDisc l X bk.ρ₀ a)) = toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev a))
      rw [hi.ext, hG.ext], fun x => (hG.norm_le _).trans (hi.norm_le x)⟩
  have hR : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ s.N • (ht.bas.map i * ε) =
      bk.iA (bk.ev bk.E) ^ s.N • ht.bas.map (G.comp i) := hrel i (G.comp i) hi hFg
  have hGA : ∀ a, G (bk.iA a) = bk.iA (Per.σA (g : GQ l) a) := hG.ext

  have hbi : ht.bas.map i = s.X.map bk.iS * ht.Z.map i := by
    rw [Height.bas, Matrix.map_mul, Matrix.map_map]
    congr 1
    ext a b
    exact hi.ext _
  have hbg : ht.bas.map (G.comp i) = (s.X.map bk.iS).map G * (ht.Z.map i).map G := by
    rw [← Matrix.map_mul, ← hbi, Matrix.map_map]; rfl

  obtain ⟨ιb, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  have he : bk.iA (bk.ev bk.E) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ιb tb).2.1
  have hL : ((l : bk.DA bk.ρ₀) ^ s.c₂) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow _).mem_nonZeroDivisors
  obtain ⟨w, hw⟩ := (_root_.GlobalTheory.BSP.hf_E_pair l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).2.1
  have hw' : bk.ev bk.E * (show Ainf l from (w : (ainfObj K).A)) = Per.σA (g : GQ l) (bk.ev bk.E) := hw
  have hwu : IsUnit (bk.iA (show Ainf l from (w : (ainfObj K).A))) := w.isUnit.map bk.iA
  have hge : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
    rw [← hw', map_mul]
    exact mul_mem he hwu.mem_nonZeroDivisors

  have hXX1 : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hXX := mul_eq_smul_comm (mul_mem hL (pow_mem he _)) hXX1
  set U := s.W * s.X'.map bk.iS with hU
  have hY : U * (s.X.map bk.iS * ht.Z.map i) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (bk.ev bk.E) ^ (2 * s.N)) • ht.Y.map bk.iA := by
    rw [hU, Matrix.mul_assoc, ← Matrix.mul_assoc (s.X'.map bk.iS), hXX, smul_mul_assoc, Matrix.one_mul,
      mul_smul_comm, ht.W_mul i hi]
  have hYG : U.map G * ((s.X.map bk.iS).map G * (ht.Z.map i).map G) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ (2 * s.N)) •
        (ht.Y.map bk.iA).map G := by
    have := congrArg (fun M => Matrix.map M G) hY
    simp only [Matrix.map_mul, map_smul_hom] at this
    rw [this, map_mul, map_pow, map_pow, map_natCast, hGA]
  have hgal := s.gal g G hG
  rw [← hU, map_mul, map_mul] at hgal
  have hgoal : (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) =
      (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (ht.Y.map bk.iA).map G := by
    rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
    congr 1
    ext a b
    exact (hGA _).symm
  rw [hgoal]
  rw [hbg] at hR
  rw [hbi] at hR
  simp only [map_mul] at hgal
  exact key (mul_mem (mul_mem hL (pow_mem hge _)) (pow_mem he _)) hY hYG hgal hR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
section
noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst

namespace GlobalTheory.TwistAbove

def twGL {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K) :
    Γ →* GL (Fin a) K where
  toFun g := ⟨((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    (((χ g)⁻¹ : Kˣ) : K) • (((r g)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K),
    by rw [smul_mul_smul_comm, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [smul_mul_smul_comm, Units.inv_mul, Units.inv_mul, one_smul]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by
    change ((χ (g * h) : Kˣ) : K) • ((r (g * h) : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)) *
      (((χ h : Kˣ) : K) • ((r h : GL (Fin a) K) : Matrix (Fin a) (Fin a) K))
    rw [smul_mul_smul_comm, map_mul, map_mul, Units.val_mul, Units.val_mul])

@[simp] theorem twGL_val {Γ K : Type} [Group Γ] [CommRing K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (g : Γ) : ((twGL χ r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      ((χ g : Kˣ) : K) • ((r g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := rfl

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a : ℕ}

abbrev chr {L : FinExt l} (m : ↥Gw →* GL (Fin 1) ↥L.1) : ↥Gw →* (↥L.1)ˣ :=
  Matrix.GeneralLinearGroup.det.comp m

theorem isModel_twGL {L : FinExt l} {r r' : ↥Gw →* GL (Fin a) (Om l)} {μ : ↥Gw →* (Om l)ˣ}
    (hr' : ∀ g, ((r' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ((μ g : (Om l)ˣ) : Om l) • ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw (rk1 μ) L m) :
    IsModel Bw r' L (twGL (chr m) r₁) := by
  refine ⟨h₁.1, ?_⟩
  ext g i j
  have e1 := congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) =>
    ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) h₁.2
  have e2 := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) =>
    ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) h₂.2
  simp only [mapRep, rk1] at e1 e2 ⊢
  simp at e1 e2 ⊢
  rw [hr']
  simp [← e1, ← e2]

section Common

variable {L : FinExt l} (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (m : ↥Gw →* GL (Fin 1) ↥L.1)

theorem repE_twGL (g : ↥(GK Bw.Kw)) (x : Fin a → ↥L.1) :
    Bw.repE L (twGL (chr m) r₁) g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • Bw.repE L r₁ g x := by
  change Matrix.toLin' ((twGL (chr m) r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x =
    ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) •
      Matrix.toLin' ((r₁ (Bw.e.symm g) : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) x
  rw [twGL_val, Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact Matrix.smul_mulVec _ _ _

theorem repE_rank_one (g : ↥(GK Bw.Kw)) (x : Fin 1 → ↥L.1) :
    Bw.repE L m g x = ((chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1) • x := by
  funext i
  fin_cases i
  simp [LocBridge.repE, Matrix.mulVec, dotProduct, Matrix.det_unique]

theorem isDR_iff (P : LocPrime l) {n : ℕ} (s : ↥Gw →* GL (Fin n) ↥L.1) :
    IsDR (P.PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE P L s := by
  rw [IsDR, LocBridge.IsdRE, Module.finrank_fin_fun]

theorem twist_common {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    (Bw.IsdRE P L r₁ → Bw.IsdRE P L m → Bw.IsdRE P L (twGL (chr m) r₁)) ∧
    (Bw.IsCrysE P L r₁ → Bw.IsCrysE P L m → Bw.IsCrysE P L (twGL (chr m) r₁)) ∧
    (Bw.IsPotCrysE P L r₁ → Bw.IsPotCrysE P L m → Bw.IsPotCrysE P L (twGL (chr m) r₁)) ∧
    ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (b : ℤ), Bw.IsdRE P L m →
      (∀ n, Bw.multE P L m τ' n = if n = b then 1 else 0) →
      ∀ n, Bw.multE P L (twGL (chr m) r₁) τ' (n + b) = Bw.multE P L r₁ τ' n := by
  have hν := repE_rank_one Bw m
  have hρ := repE_twGL Bw r₁ m
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, ?_, ?_⟩
  · rw [← isDR_iff] at h1 h2 ⊢
    exact (GlobalTheory.TwistDR.isDR_twist_iff l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ h2).1 h1
  · exact (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T Bw.Kw L (Fin a → ↥L.1)
      _ _ _ _ hν hρ h2).1 h1
  · rintro ⟨K₁, k₁, c₁⟩ ⟨K₂, k₂, c₂⟩
    have l₁ : K₁.1 ≤ (supExt K₁ K₂).1 := le_sup_left
    have l₂ : K₂.1 ≤ (supExt K₁ K₂).1 := le_sup_right
    have k₃ : Bw.Kw.1 ≤ (supExt K₁ K₂).1 := k₁.trans l₁
    have d₁ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₁ _ T c₁
    have d₂ := GlobalTheory.Per.TiedRestrict.isCrys_restrict l₂ _ T c₂
    have e₁ : ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₁))).comp (Subgroup.inclusion (GK_le l₁)) =
        (Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    have e₂ : ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₂))).comp (Subgroup.inclusion (GK_le l₂)) =
        (Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃)) := MonoidHom.ext fun _ => rfl
    rw [e₁] at d₁
    rw [e₂] at d₂
    exact ⟨supExt K₁ K₂, k₃, (GlobalTheory.TwistCrys.isCrys_iff_of_twist GlobalTheory.MemLoc.fontaineBcris l P AI T
      (supExt K₁ K₂) L (Fin a → ↥L.1) ((Bw.repE L r₁).comp (Subgroup.inclusion (GK_le k₃))) _
      ((Bw.repE L m).comp (Subgroup.inclusion (GK_le k₃))) _ (fun g x => hν _ x) (fun g x => hρ _ x) d₂).1 d₁⟩
  · intro τ' b hm hmult n
    exact GlobalTheory.TwistJump.multV_twist_char l P AI T Bw.Kw L (Fin a → ↥L.1) _ _ _ _ hν hρ
      ((isDR_iff Bw P m).2 hm) τ' b hmult n

end Common

theorem twist_above : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ), ∀ (r r' : ↥Gw →* GL (Fin a) (Loc.Om l)) (μ : ↥Gw →* (Loc.Om l)ˣ), (∀ g, ((r' g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) = ((μ g : (Loc.Om l)ˣ) : Loc.Om l) • ((r g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l))) → (IsdRAt P Bw r → IsdRAt P Bw (rk1 μ) → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw (rk1 μ) → IsCrysAt P Bw r') ∧ (IsPotCrysAt P Bw r → IsPotCrysAt P Bw (rk1 μ) → IsPotCrysAt P Bw r') ∧ ∀ (τ : E →+* Loc.Om l) (J : Multiset ℤ) (c : ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw (rk1 μ) τ {c} → IsJumpsAt P Bw r' τ (J.map (· + c)) := by
  intro l _ P AI hT E Ω _ _ _ _ Gw O _ _ _ Bw a r r' μ hr'
  obtain ⟨T⟩ := hT
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun τ J c h1 h2 => ?_⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.1 ((local_ext P Bw l₁ r₁).1.2 d₁) ((local_ext P Bw l₂ r₂).1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    exact ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      (twist_common Bw _ _ T).2.2.1 ((local_ext P Bw l₁ r₁).2.2.1.2 d₁) ((local_ext P Bw l₂ r₂).2.2.1.2 d₂)⟩
  · obtain ⟨L₁, r₁, m₁, d₁, τ₁, i₁, c₁⟩ := h1
    obtain ⟨L₂, r₂, m₂, d₂, τ₂, i₂, c₂⟩ := h2
    have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
    have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
    have j₁ : IsInduced Bw τ ((IntermediateField.inclusion l₁).comp τ₁) := fun x => i₁ x
    have j₂ : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ₂) := fun x => i₂ x
    have eτ := IsInduced.unique j₁ j₂
    have hd₂ := (local_ext P Bw l₂ r₂).2.1.2 d₂
    have hc := twist_common Bw (mapRep (IntermediateField.inclusion l₁).toRingHom r₁)
      (mapRep (IntermediateField.inclusion l₂).toRingHom r₂) T
    have hm : ∀ n, Bw.multE P (supExt L₁ L₂) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
        ((IntermediateField.inclusion l₁).comp τ₁) n = if n = c then 1 else 0 := by
      intro n
      rw [eτ, (local_ext P Bw l₂ r₂).2.2.2 τ₂ n, ← c₂ n, Multiset.count_singleton]
      split_ifs <;> simp
    refine ⟨_, _, isModel_twGL Bw hr' (m₁.enlarge l₁) (m₂.enlarge l₂),
      hc.1 ((local_ext P Bw l₁ r₁).2.1.2 d₁) hd₂, _, j₁, fun n => ?_⟩
    have e1 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) J (add_left_injective c) (n - c)
    simp only [sub_add_cancel] at e1
    have e2 := hc.2.2.2 _ c hd₂ hm (n - c)
    rw [sub_add_cancel] at e2
    rw [e1, e2, (local_ext P Bw l₁ r₁).2.2.2 τ₁ (n - c), c₁]

end GlobalTheory.TwistAbove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodCocycleFrobeniusRelationOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_cocycle_frobenius_relation_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ := by
  first | (exact @GlobalTheory.BKLim.KappaFrob.main) | (exact GlobalTheory.BKLim.KappaFrob.main) | (intros; apply GlobalTheory.BKLim.KappaFrob.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameCocycleFrobeniusTwistOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  first | (exact @GlobalTheory.BKLim.FrobTwistKappa.main) | (exact GlobalTheory.BKLim.FrobTwistKappa.main) | (intros; apply GlobalTheory.BKLim.FrobTwistKappa.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameFrobeniusIsUnitDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_frame_frobenius_isUnit_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → IsUnit Z → IsUnit (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * (s.X.map (toDisc l (X : bk.S) bk.ρ₀) * Z).map Ψ) := by
  first | (exact @GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit) | (exact GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit) | (intros; apply GlobalTheory.BKLim.wseed_F_frob_XZ_isUnit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusOfScaledInverseStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_frobenius_of_scaled_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  first | exact @GlobalTheory.BKLim.wseed_frob_inverse | exact GlobalTheory.BKLim.wseed_frob_inverse | (intros; apply GlobalTheory.BKLim.wseed_frob_inverse; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrobeniusRationalOverKisinRingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_frobenius_rational_over_kisinRing : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  first | (exact @GlobalTheory.BKLim.FrobRational.main) | (exact GlobalTheory.BKLim.FrobRational.main) | (intros; apply GlobalTheory.BKLim.FrobRational.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodSpanFrobeniusStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriod_span_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  first | exact @GlobalTheory.BKLim.wseed_span_frobenius_stable | exact GlobalTheory.BKLim.wseed_span_frobenius_stable | (intros; apply GlobalTheory.BKLim.wseed_span_frobenius_stable; all_goals assumption)
end

