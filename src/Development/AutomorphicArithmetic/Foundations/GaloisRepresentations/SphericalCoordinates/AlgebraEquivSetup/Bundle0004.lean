module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CompLocOfApart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

def OHat (p : ℕ) (E : Type) [Field E] [NumberField E] : AddSubgroup (AfP p ⊗[ℚ] E) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ (x : E)}

structure AdQ (p : ℕ) where
  ρ : AfQ →+* AfP p
  surj : Function.Surjective ρ
  ker : ∀ a, ρ a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0
  int : ∀ a, IsIntAf (ρ a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1

structure AdT (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] extends AdQ p where
  Φ : Af E →+* AfP p ⊗[ℚ] E
  Φ_E : ∀ x : E, Φ (algebraMap E (Af E) x) = 1 ⊗ₜ x
  Φ_Q : ∀ a : AfQ, Φ (finiteAdeleMap ℚ E a) = ρ a ⊗ₜ 1
  Φ_surj : Function.Surjective Φ
  Φ_ker : ∀ x, Φ x = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0
  Φ_int : ∀ x, Φ x ∈ OHat p E ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → Valued.v (pLoc E w x) ≤ 1
  Φ_conj : ∀ x, Φ (conjFin (conjE E) x) = conjT E (AfP p) (Φ x)

def AdQEx : Prop := ∀ (p : ℕ) [Fact p.Prime], Nonempty (AdQ p)

def AdTensor : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ ι : AfQ ⊗[ℚ] E ≃+* Af E,
  (∀ (a : AfQ) (x : E), ι (a ⊗ₜ x) = finiteAdeleMap ℚ E a * algebraMap E (Af E) x) ∧
  (∀ y, y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} ↔
    ∀ w : Plc E, Valued.v (pLoc E w (ι y)) ≤ 1) ∧
  ∀ a : AfQ, conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a

def IdemP : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E], ∃ e : AfQ,
  (∀ v : Plc ℚ, ((p : 𝓞 ℚ) ∈ v.asIdeal → e v = 1) ∧ ((p : 𝓞 ℚ) ∉ v.asIdeal → e v = 0)) ∧
  ∀ w : Plc E, ((p : 𝓞 E) ∈ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 1) ∧
    ((p : 𝓞 E) ∉ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 0)

def AdTEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E], Nonempty (AdT p E)

def IsMu {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : Prop :=
  ∀ (r : R) (x : Matrix (Fin n) (Fin n) E) i k, μ (r ⊗ₜ x) i k = r ⊗ₜ x i k

def MuEx : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ),
  ∃ μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E), IsMu μ

def MuStar : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)), IsMu μ → ∀ x,
  Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ (starT (hermStar (A.H n) (A.det_ne n)) R x).unop =
    ((μ x).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsIso (A : Arith E) (n : ℕ) (a : GL (Fin n) (Af E)) : Prop :=
  (a.val.map (conjFin (conjE E)))ᵀ * Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) * a.val = 1 ∧
    ∀ (w : Plc E) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal → GeneralLinearGroup.map (pLoc E w) a ∈ KGL w (n := n)

def Arith.β₀ (A : Arith E) (n : ℕ) : (Matrix (Fin n) (Fin n) E)ˣ :=
  GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (A.dg n i : E)) (by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this])

variable {A : Arith E} {n p : ℕ} [Fact p.Prime]

def Setup.mx (S : Setup A n p) (h : S.G.GAf) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ((h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] S.G.C)

structure Tr (S : Setup A n p) extends AdT p E where
  μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)
  mu : IsMu μ
  a : GL (Fin n) (Af E)
  iso : IsIso A n a
  j : GUf E n →* S.G.GAf
  j_mx : ∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map Φ
  j_sim : ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = ρ (sim g : AfQˣ)
  sec : S.G.GAf →* GUf E n
  j_sec : ∀ h, j (sec h) = h
  sec_p : ∀ h (w : Plc E), (p : 𝓞 E) ∈ w.asIdeal → comp w (sec h) = 1
  j_eq : ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∃ j : GUf E n →* S.G.GAf,
    (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) ∧
    ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = T.ρ (sim g : AfQˣ)

def JEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ (a : GL (Fin n) (Af E)) (j : GUf E n →* S.G.GAf), (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) →
  (∀ g g' : GUf E n, (∀ w, comp w g = comp w g') → g = g') ∧
  ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JSurj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∀ h : S.G.GAf, ∃ g : GUf E n,
    μ (S.mx h) = (a * mat g * a⁻¹).val.map T.Φ ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g = 1

def IsoEx' : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Odd n → ∃ a, IsIso A n a

def TrEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p),
  Odd n → Nonempty (Tr S)

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (hw : IsSplitAt w)
  (x : GL (Fin n) (w.adicCompletion E)) (g : GUf E n), comp w g = 1 → CertificateRingHomMap.loc hw x * g = g * CertificateRingHomMap.loc hw x

theorem apart_of_not_mem {w u : Plc E} (hw : (p : 𝓞 E) ∉ w.asIdeal) (hu : (p : 𝓞 E) ∈ u.asIdeal) : GlobalTheory.Cong.Apart u w := by
  intro h
  apply hw
  have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simpa using hu
  rw [h] at h1
  have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := h1
  simpa using h2

def Tr.at {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    Loc S.G.GAf (GL (Fin n) (w.adicCompletion E)) where
  pr := (comp w).comp T.sec
  loc := T.j.comp (CertificateRingHomMap.loc hw)
  pr_loc x := by
    have := (T.j_eq (T.sec (T.j (CertificateRingHomMap.loc hw x))) (CertificateRingHomMap.loc hw x)).1 (T.j_sec _) w hp
    simpa using this
  comm x g h := by
    have := congrArg T.j (hc E n w hw x (T.sec g) h)
    simpa [T.j_sec] using this

def LatCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∃ ν : AfP p ⊗[ℚ] VQ S.D ≃+ (Fin n → AfP p ⊗[ℚ] E),
    (∀ (r : AfP p) (v : Fin n → 𝓞 E) i, ν (r ⊗ₜ ((1 : ℚ) ⊗ₜ[ℤ] v)) i = r ⊗ₜ (v i : E)) ∧
    (∀ h v, ν (S.L.actG h v) = μ (S.mx h) *ᵥ ν v) ∧ ∀ v, v ∈ LaHat S.D ↔ ∀ i, ν v i ∈ OHat p E

def Cong1 (N : ℕ) (w : Plc E) (x : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∀ i k, Valued.v ((x.val - 1) i k) ≤ Valued.v (N : w.adicCompletion E)

def KNIff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n),
  ((∀ v ∈ LaHat S.D, S.L.actG (T.j g) v ∈ LaHat S.D) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k,
    Valued.v ((GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val i k) ≤ 1) ∧
  ∀ N : ℕ, 0 < N → (S.L.CongOne N (T.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)))

def StdForm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1) (e : GlobalTheory.LKCx.grp S.G B.β →* Gam0 E n),
    (∀ y, ((e y : Gam0 E n) : GL (Fin n) E × ℚˣ) = (y : S.G.Cˣ × ℚˣ)) ∧ ∀ y, GlobalTheory.LKCx.toAfF S.G B.β x 1 hx y = T.j (rat (e y))

def PInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G →
  (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w (n := n)) ∧
    ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∈ v.asIdeal → Valued.v (((sim (rat y) : AfQˣ) : AfQ) v) = 1

end UpperTheory.Gal.W2.Seed
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ExistsClose
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma exists_close {E : Type} [Field E] [NumberField E] (c : InfinitePlace E → E) :
    ∃ x : E, ∀ v : InfinitePlace E, v (x - c v) < 1 / 2 := by
  have hd := InfinitePlace.denseRange_algebraMap_pi E
  obtain ⟨x, hx⟩ := hd.exists_dist_lt (fun v : InfinitePlace E => WithAbs.toAbs v.1 (c v))
    (by norm_num : (0:ℝ) < 1/2)
  refine ⟨x, fun v => ?_⟩
  have h1 := (dist_le_pi_dist _ _ v).trans_lt hx
  rw [dist_comm, dist_eq_norm] at h1
  exact h1

theorem UpperTheory.Gal.W2.Seed.pCEx :
    CEx := by
  intro E _ _ _ τ₀ M hM
  classical
  obtain ⟨x, hx⟩ := exists_close (E := E) (fun v => if v = InfinitePlace.mk τ₀ then -1 else 1)
  have hbound : ∀ τ : E →+* ℂ,
      |(τ x).re - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1)| < 1 / 2 := by
    intro τ
    have h : ‖τ (x - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1))‖ < 1 / 2 :=
      hx (InfinitePlace.mk τ)
    refine lt_of_le_of_lt ?_ h
    split_ifs with hτ
    · have := Complex.abs_re_le_norm (τ x - -1)
      simpa using this
    · have := Complex.abs_re_le_norm (τ x - 1)
      simpa using this
  have hxalg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple hxalg
  set z : E := y • (y • x) with hzdef
  have hz : IsIntegral ℤ z := hyint.smul y
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have hy2 : 0 < (y : ℝ) ^ 2 := by positivity
  have hτz : ∀ τ : E →+* ℂ, (τ z).re = (y : ℝ) ^ 2 * (τ x).re := by
    intro τ
    simp [hzdef, zsmul_eq_mul]
    ring
  set w : E := z + IsCMField.complexConj E z with hwdef
  have hw : IsIntegral ℤ w := hz.add (map_isIntegral_int (IsCMField.complexConj E) hz)
  have hτw : ∀ τ : E →+* ℂ, (τ w).re = 2 * (τ z).re := by
    intro τ
    simp [hwdef, IsCMField.complexEmbedding_complexConj]
    ring
  have hneg : (τ₀ w).re < 0 := by
    have hb := hbound τ₀
    rw [if_pos rfl] at hb
    have := (abs_lt.mp hb).2
    rw [hτw, hτz]
    nlinarith
  have hpos : ∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ w).re := by
    intro τ hτ
    have hb := hbound τ
    rw [if_neg hτ] at hb
    have := (abs_lt.mp hb).1
    rw [hτw, hτz]
    nlinarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ((M : ℝ) * -(τ₀ w).re))
  have hKM : 1 < (M : ℝ) * K * -(τ₀ w).re := by
    have hd : 0 < (M : ℝ) * -(τ₀ w).re := by nlinarith
    rw [div_lt_iff₀ hd] at hK
    nlinarith
  let wO : 𝓞 E := ⟨w, (mem_integralClosure_iff ℤ E).mpr hw⟩
  have hcoe : (((1 : 𝓞 E) + (M : 𝓞 E) * ((K : 𝓞 E) * wO) : 𝓞 E) : E) = 1 + (M : E) * ((K : E) * w) := by
    push_cast
    rfl
  have hre : ∀ τ : E →+* ℂ, (τ (1 + (M : E) * ((K : E) * w))).re = 1 + (M : ℝ) * K * (τ w).re := by
    intro τ
    simp
    ring
  refine ⟨1 + (M : 𝓞 E) * ((K : 𝓞 E) * wO), ?_, ?_, ?_, (K : 𝓞 E) * wO, rfl⟩
  · rw [hcoe]
    simp [hwdef, add_comm]
  · rw [hcoe, hre]
    linarith
  · intro τ hτ
    rw [hcoe, hre]
    have := hpos τ hτ
    have : 0 ≤ (M : ℝ) * K * (τ w).re := by positivity
    linarith
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HenselRoot
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma hensel_root (p : ℕ) [Fact p.Prime] (tr nm r : ℤ) (hd : ¬ (p : ℤ) ∣ tr ^ 2 - 4 * nm)
    (hr : (p : ℤ) ∣ r ^ 2 - tr * r + nm) :
    ∃ ρ : ℤ_[p], ρ ^ 2 - (tr : ℤ_[p]) * ρ + (nm : ℤ_[p]) = 0 := by
  have hF1 : ¬ (p : ℤ) ∣ 2 * r - tr := by
    intro h
    apply hd
    have h2 : (p : ℤ) ∣ (2 * r - tr) ^ 2 := dvd_pow h two_ne_zero
    have h3 : (p : ℤ) ∣ 4 * (r ^ 2 - tr * r + nm) := dvd_mul_of_dvd_right hr 4
    have h4 := dvd_sub h2 h3
    have : (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm := by ring
    rwa [this] at h4
  set F : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.C tr * Polynomial.X + Polynomial.C nm with hFdef
  have hval : Polynomial.aeval (r : ℤ_[p]) F = ((r ^ 2 - tr * r + nm : ℤ) : ℤ_[p]) := by
    simp [hFdef]
  have hder : Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F) = ((2 * r - tr : ℤ) : ℤ_[p]) := by
    simp [hFdef]
    left
    exact map_ofNat _ 2
  have hn1 : ‖Polynomial.aeval (r : ℤ_[p]) (Polynomial.derivative F)‖ = 1 := by
    rw [hder]
    refine le_antisymm (PadicInt.norm_le_one _) ?_
    by_contra hlt
    push_neg at hlt
    exact hF1 ((PadicInt.norm_int_lt_one_iff_dvd _).1 hlt)
  have hn0 : ‖Polynomial.aeval (r : ℤ_[p]) F‖ < 1 := by
    rw [hval]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hr
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := (r : ℤ_[p])) (by rw [hn1]; simpa using hn0)
  refine ⟨z, ?_⟩
  simpa [hFdef] using hz

theorem UpperTheory.Gal.W2.Seed.pUEx :
    UEx := by
  intro E _ _ _ A p _ hsplit Kq hω hspan τ
  unfold Arith.SplitK at hsplit
  obtain ⟨hd, r, hr⟩ := hsplit
  obtain ⟨ρ, hρ⟩ := hensel_root p A.tr A.nm r hd hr
  set ι := algebraMap ℚ_[p] (PadicAlgCl p) with hι
  have hinj : Function.Injective ι := ι.injective
  set w := τ ((A.ω : 𝓞 E) : E) with hwdef
  have h0 : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]
    ring
  have h1 : ((A.ω : E)) ^ 2 - (A.tr : E) * (A.ω : E) + (A.nm : E) = 0 := by
    have := congrArg (fun x : 𝓞 E => (x : E)) h0
    simpa using this
  have hw : w ^ 2 - (A.tr : PadicAlgCl p) * w + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg τ h1
    simpa [hwdef] using this
  have hc : ι (ρ : ℚ_[p]) ^ 2 - (A.tr : PadicAlgCl p) * ι (ρ : ℚ_[p]) + (A.nm : PadicAlgCl p) = 0 := by
    have := congrArg (fun t : ℤ_[p] => ι (t : ℚ_[p])) hρ
    simpa using this
  have hprod : (w - ι (ρ : ℚ_[p])) * (w - ((A.tr : PadicAlgCl p) - ι (ρ : ℚ_[p]))) = 0 := by
    linear_combination hw - hc
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℤ_[p], w = ι (ρ₀ : ℚ_[p]) := by
    rcases mul_eq_zero.1 hprod with h | h
    · exact ⟨ρ, sub_eq_zero.1 h⟩
    · refine ⟨(A.tr : ℤ_[p]) - ρ, ?_⟩
      rw [sub_eq_zero.1 h]
      simp
  have hex : ∀ x : Kq, ∃ q : ℚ_[p], ι q = τ (x : E) := by
    intro x
    obtain ⟨a, b, hab⟩ := hspan x x.2
    refine ⟨(a : ℚ_[p]) + (b : ℚ_[p]) * (ρ₀ : ℚ_[p]), ?_⟩
    rw [hab]
    simp [← hρ₀, hwdef]
  choose f hf using hex
  let u : Kq →+* ℚ_[p] :=
    { toFun := f
      map_one' := hinj (by rw [hf]; simp)
      map_mul' := fun x y => hinj (by rw [hf, map_mul, hf, hf]; simp)
      map_zero' := hinj (by rw [hf]; simp)
      map_add' := fun x y => hinj (by rw [hf, map_add (f := _), hf, hf]; simp) }
  refine ⟨u, ρ₀, ?_, ?_⟩
  · unfold LiesOver
    intro x
    exact (hf x).symm
  · apply hinj
    show ι (f ⟨_, hω⟩) = _
    rw [hf, ← hρ₀]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtPEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAtPEx :
    KqEx → UEx → OrbEx → LiftEx → AtPEx := by
  intro hK hU hO hL E _ _ _ A p _ hs
  obtain ⟨Kq, hω, hKq, hgen⟩ := hK E A
  obtain ⟨s, iotaC, hsC⟩ := hL E A.τ₀
  haveI : CharZero (PadicAlgCl p) := charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.isAlgebraic ℚ)
  let iotaA : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p := iotaA.toRingHom
  let τ₁ : E →+* PadicAlgCl p := iotaP.comp s
  obtain ⟨u, ρ, hover, hρ⟩ := hU E A p hs Kq hω hgen τ₁
  obtain ⟨m, emb, w, hw, hov, hinj, hall⟩ := hO E p Kq u τ₁ hover
  exact ⟨{ Kq := Kq, hKq := hKq, u := u, m := m, emb := emb, emb_over := hov, emb_inj := hinj, emb_all := hall,
           iotaP := iotaP, iotaC := iotaC, ρp := ρ, ρp_eq := ⟨hω, hρ⟩, s := s, s_C := hsC, w := w,
           s_P := fun x => by rw [hw]; rfl }⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PBarEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pBarEx :
    BarEx := by
  intro E _ _ _
  refine ⟨(IsCMField.ringOfIntegersComplexConj E).toRingEquiv, fun a => ?_⟩
  exact IsCMField.coe_ringOfIntegersComplexConj E a
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffUnit
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pCodiffUnit :
    UnitMod → CodiffUnit := by
  intro hU E _ _ M hMpos y t hy ht hloc
  obtain ⟨_, e, he, hye⟩ := hy
  by_cases hM1 : M = 1
  · refine ⟨ht, 0, by simp [hM1], fun z _ => ⟨0, by simp⟩⟩
  let A : Ideal (𝓞 E) :=
    { carrier := {a | ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x}
      add_mem' := by
        intro a b ha hb z hz
        obtain ⟨x1, h1⟩ := ha z hz
        obtain ⟨x2, h2⟩ := hb z hz
        exact ⟨x1 + x2, by push_cast; rw [add_mul, h1, h2, mul_add]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro c a ha z hz
        obtain ⟨x, hx⟩ := ha z hz
        refine ⟨c * x, ?_⟩
        simp only [smul_eq_mul]
        push_cast
        rw [mul_assoc, hx]
        ring }
  have hA : ∀ a : 𝓞 E, a ∈ A → ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x :=
    fun a ha => ha
  have htop : A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMP : ((M : ℕ) : 𝓞 E) ∈ P :=
      hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨s, u, _, huP, hsu⟩ := hloc P hPmax hMP
    have heP : ((e : ℕ) : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr he
      have h1 : ((p : 𝓞 E) * ((e : ℕ) : 𝓞 E) + (q : 𝓞 E) * ((M : ℕ) : 𝓞 E)) = 1 := by
        have := congrArg (fun n : ℤ => (n : 𝓞 E)) hpq
        push_cast at this
        exact this
      apply hPmax.ne_top
      rw [Ideal.eq_top_iff_one, ← h1]
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hue : u * ((e : ℕ) : 𝓞 E) ∉ P := by
      intro hmem
      rcases hPmax.isPrime.mem_or_mem hmem with h | h
      · exact huP h
      · exact heP h
    apply hue
    apply hle
    apply Ideal.mem_sup_left
    intro z hz
    obtain ⟨x, hx⟩ := hye z hz
    refine ⟨s * x, ?_⟩
    push_cast
    rw [mul_assoc, hx, ← mul_assoc, ← hsu]
    ring
  have hone : (1 : 𝓞 E) ∈ A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, haA, m, hm, ham⟩ := Submodule.mem_sup.mp hone
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hm
  by_cases ha0 : a = 0
  · exfalso
    apply hM1
    have hunit : IsUnit ((M : ℕ) : 𝓞 E) :=
      isUnit_iff_exists_inv.mpr ⟨b, by rw [ha0, zero_add] at ham; rw [mul_comm]; exact ham⟩
    have hspan : Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) M
    rw [hspan, Ideal.absNorm_top] at hn
    have hpos : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
    rcases Nat.pow_eq_one.mp hn.symm with h | h
    · exact h
    · exact absurd h hpos
  obtain ⟨e', he', c', hc'⟩ := hU E M a (-b) ha0 (by linear_combination ham)
  refine ⟨ht, e', he', fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := hA a haA z hz
  refine ⟨c' * x, ?_⟩
  have hcoe : ((e' : ℕ) : E) = (a : E) * (c' : E) := by
    have := congrArg (fun w : 𝓞 E => (w : E)) hc'
    push_cast at this
    exact this.symm
  rw [hcoe, mul_comm (a : E), mul_assoc, hx]
  push_cast
  ring
end

