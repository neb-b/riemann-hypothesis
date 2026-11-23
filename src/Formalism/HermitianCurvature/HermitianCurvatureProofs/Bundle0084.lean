module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def CapEig (P : M.Par) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (ρ : M.Ty P) (X : Wq →L[ℂ] Wp) : Prop :=
  ∀ (Y : ℂ) (v : Wq), X (qdet (Qr.EB π' Fr) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • X v

def FibAt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (g : Q.Mx k r) : Set (Wq →L[ℂ] Wp) :=
  {X | ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', h * g * h' = g → (π h).comp (X.comp (π' h')) = X}

end preds

def KLEig : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qρ : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qρ →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr →
    ∀ (ρ : M.Ty P), ∀ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      (E.comp (Qρ ρ) = E ↔ CapEig P Bs.π' Fr ρ E)

def KLAtMost : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ (ρ : M.Ty P) (E Z : Wq →L[ℂ] Wp), E ∈ FibAt P.k P.r z z' π π' g → Z ∈ FibAt P.k P.r z z' π π' g →
      CapEig P π' Fr ρ E → CapEig P π' Fr ρ Z → E ≠ 0 → ∃ c : ℂ, Z = c • E

def KLExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ ρ : M.Ty P, ∃ E ∈ FibAt P.k P.r z z' π π' g, CapEig P π' Fr ρ E ∧ E ≠ 0

def KLIsoAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V')
    (m : Fin n → ℂ), GlRel E → GlRel E' → Qr.Irr E → Qr.Irr E' → Qr.SDec m →
    (∀ (w : ℂ) (v : V), qdet E w v = Qr.cpol m w • v) → (∀ (w : ℂ) (v : V'), qdet E' w v = Qr.cpol m w • v) →
    ∃ A : V' →ₗ[ℂ] V, A ≠ 0 ∧ ∀ a b, A ∘ₗ E' a b = E a b ∘ₗ A

def KLLieGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → Qr.IsRepW k r z π → Qr.IsRepW k r z' π' →
    ∀ g : Q.Mx k r, g ∈ Q.Glev k r (Fin.last r) → Q.GGl k r z z' g ≠ 0 →
    ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ A : Wq →L[ℂ] Wp, (∀ (a b : Fin (k - 1)) (v : Wq), A (Qr.EB π' Fr a b v) = Qr.EB π (fun i => g *ᵥ Fr i) a b (A v)) →
      A ∈ FibAt k r z z' π π' g

def KLExistsOf : Prop := KLIsoAlg → KLLieGrp → KLExists

def GTKLineOfCut : Prop := KLEig → KLAtMost → KLExists → GTKLine

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem fib_iff_fibAt {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {ζ : ℂ} {X : Wq →L[ℂ] Wp} :
    X ∈ NF.Fib k r z z' μsec π π' ζ ↔ X ∈ FibAt k r z z' π π' (NF.muZ k r μsec ζ) := by
  first
  | exact Iff.rfl
  | (simp only [NF.Fib, FibAt, Set.mem_setOf_eq, NF.Stab, Prod.forall]
     constructor
     · intro h a ha b hb hab
       exact h a b ⟨ha, hb, hab⟩
     · rintro h a b ⟨ha, hb, hab⟩
       exact h a ha b hb hab)

theorem fibAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {g : Q.Mx k r} {X : Wq →L[ℂ] Wp} (hX : X ∈ FibAt k r z z' π π' g) (c : ℂ) :
    c • X ∈ FibAt k r z z' π π' g := by
  simp only [FibAt, Set.mem_setOf_eq] at hX ⊢
  intro h hh h' hh' hg
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX h hh h' hh' hg]

theorem capEig_smul {P : M.Par} {π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ} {ρ : M.Ty P} {X : Wq →L[ℂ] Wp}
    (hX : CapEig (Wp := Wp) P π' Fr ρ X) (c : ℂ) : CapEig P π' Fr ρ (c • X) := by
  unfold CapEig at hX ⊢
  intro Y v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hX Y v, smul_comm]

end asm

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_ne_zero {A : Wq →L[ℂ] Wp} (hA : A ≠ 0) : B.hsVec A ≠ 0 := by
  intro h
  apply hA
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have h2 := congrArg
      (fun x : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) => (WithLp.ofLp x : Fin _ → Wp) i) h
    simpa [B.hsVec] using h2
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)

end hs

theorem gTKLine_of_cut : GTKLineOfCut := by
  intro hEig hAt hEx Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ ρ
  obtain ⟨hpl, hk, hcs, -, -, -, -⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hg : g ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb hcs.1 hζ')
  have hGG : Q.GGl P.k P.r Bs.z Bs.z' g ≠ 0 := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' hcs.1 hζ']
    linarith
  obtain ⟨-, -, Fr, -, -, -, hFr, -⟩ := Formalism.FourierDecayAlt.P.Qx8.geom_at hOK.k_pos hz hz' hT hT' hg hGG
  obtain ⟨E0, hE0f, hE0e, hE0n⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ
  set s : ℝ := ‖B.hsVec E0‖ with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact norm_ne_zero_iff.mpr (hsVec_ne_zero hE0n)
  set E : Wq →L[ℂ] Wp := ((s : ℂ)⁻¹) • E0 with hEdef
  have hEf : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := fib_iff_fibAt.mpr (fibAt_smul hE0f _)
  have hEe : CapEig P Bs.π' Fr ρ E := capEig_smul hE0e _
  have hEn : E ≠ 0 := by
    rw [hEdef]
    exact smul_ne_zero (inv_ne_zero (by exact_mod_cast hs0)) hE0n
  have hunit : inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) := by
    rw [hEdef, hsVec_smul, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, ← hs]
    simp only [map_inv₀, Complex.conj_ofReal]
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    field_simp
    rfl
  refine ⟨E, hEf, (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hEf).mpr hEe, hunit, fun Z hZf hZq => ?_⟩
  have hZe : CapEig P Bs.π' Fr ρ Z := (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ Z hZf).mp hZq
  obtain ⟨c, hc⟩ := hAt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ E Z
    (fib_iff_fibAt.mp hEf) (fib_iff_fibAt.mp hZf) hEe hZe hEn
  have hi : inner ℂ (B.hsVec E) (B.hsVec Z) = c := by
    rw [hc, hsVec_smul c E, inner_smul_right, hunit, mul_one]
  rw [hi]
  exact hc

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCapSmooth
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CapSm

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def glW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    Submodule ℂ (Mx k r) where
  carrier := {Z | Qr.InGlW k r z Z}
  add_mem' := fun {Z Z'} hZ hZ' => (elementary_lie_elements Wp k r z π hπ Z Z' hZ hZ').1.1
  zero_mem' := by
    have h := LieListProducts.gl_comb (LieListProducts.lie_zero (k := k) (r := r) (z := z)) (LieListProducts.lie_zero (k := k) (r := r) (z := z))
    simpa using h
  smul_mem' := fun c Z hZ => ((elementary_lie_elements Wp k r z π hπ Z Z hZ hZ).2.1 c).1

def ecL (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    glW k r z π hπ →ₗ[ℂ] (Wp →L[ℂ] Wp) where
  toFun Z := QrD.ecOp π Z.1
  map_add' Z Z' := (elementary_lie_elements Wp k r z π hπ Z.1 Z'.1 Z.2 Z'.2).1.2
  map_smul' c Z := ((elementary_lie_elements Wp k r z π hπ Z.1 Z.1 Z.2 Z.2).2.1 c).2

theorem foldr_apply (l : List (Wp →L[ℂ] Wp)) (v : Wp) :
    List.foldr (fun (T : Wp → Wp) h => T h) v (List.map (fun T : Wp →L[ℂ] Wp => (⇑T : Wp → Wp)) l) =
      (l.foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1) v := by
  induction l with
  | nil => simp
  | cons T l ih =>
    simp only [List.map_cons, List.foldr_cons, ContinuousLinearMap.comp_apply, ih]

theorem foldr_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (l : List (X → (Wp →L[ℂ] Wp)))
    (h : ∀ f ∈ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (l.map fun f => f x).foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (Wp →L[ℂ] Wp) × (Wp →L[ℂ] Wp) => p.1.comp p.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := Wp) (F := Wp) (G := Wp)).contDiff.restrict_scalars ℝ
  induction l with
  | nil => simpa using contDiff_const
  | cons f l ih =>
    have hf := h f (List.mem_cons_self ..)
    have hl := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
    simp only [List.map_cons, List.foldr_cons]
    exact hc.comp (hf.prodMk hl)

theorem unitB_contDiff {m : ℕ} (a b : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Bs : Fin m → Fin (2 * r + k + 1) → ℂ => unitB (Hpk k r) Bs a b) := by
  unfold unitB
  refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Pi.star_apply]
  refine ContDiff.mul (contDiff_apply_apply ℝ a p)
    (ContDiff.sum fun i _ => ?_)
  exact (Complex.conjCLE.contDiff.comp
    (contDiff_apply_apply ℝ b i)).mul contDiff_const

end CapSm

open CapSm in
theorem capacity_smoothness_holds : CapSmooth := by
  intro Wp _ _ _ k r m z π hπ w
  obtain ⟨G', hG'⟩ := Submodule.exists_isCompl (glW k r z π hπ)
  let Lext : Mx k r →ₗ[ℂ] (Wp →L[ℂ] Wp) := (ecL z π hπ).comp (Submodule.linearProjOfIsCompl _ _ hG')
  have hLext : ∀ Z (hZ : Qr.InGlW k r z Z), Lext Z = QrD.ecOp π Z := by
    intro Z hZ
    have hmem : Z ∈ glW k r z π hπ := hZ
    have e := Submodule.linearProjOfIsCompl_apply_left hG' ⟨Z, hmem⟩
    show ecL z π hπ (Submodule.linearProjOfIsCompl _ _ hG' Z) = _
    erw [e]
    rfl
  let Lc : Mx k r →L[ℂ] (Wp →L[ℂ] Wp) := LinearMap.toContinuousLinearMap Lext
  have hLc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Z : Mx k r => Lc Z) := (Lc.restrictScalars ℝ).contDiff
  let T : Equiv.Perm (Fin m) → Fin m → (Fin m → Fin (2 * r + k + 1) → ℂ) → (Wp →L[ℂ] Wp) := fun σ t Bs =>
    (if σ t = t then (w - ((t : ℕ) : ℂ)) • (1 : Wp →L[ℂ] Wp) else 0) + Lc (unitB (Hpk k r) Bs (σ t) t)
  refine ⟨fun Bs => ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
    ((List.ofFn fun t => T σ t).map fun f => f Bs).foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1, ?_, ?_⟩
  · refine ContDiff.sum fun σ _ => ContDiff.const_smul _ ?_
    refine foldr_contDiff _ fun f hf => ?_
    obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hf
    exact contDiff_const.add (hLc.comp (unitB_contDiff _ _))
  · intro Bs hB v
    unfold capRep qmF
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearMap.smul_apply, ← foldr_apply]
    congr 2
    simp only [List.map_ofFn]
    congr 1
    funext t y
    have hl := QrD.frame_lie hB (σ t) t
    have hgl : Qr.InGlW k r z (unitB (Hpk k r) Bs (σ t) t) := hl
    simp only [Function.comp_apply, T, id]
    rw [ContinuousLinearMap.add_apply, QrD.ecRep_eq hπ.1 hπ.2 hl.1 hl.2 (k := k) (r := r), ← hLext _ hgl]
    congr 1
    split_ifs <;> simp

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoEigOrth
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace EigenvectorOrthogonality

variable {k r : ℕ}

private theorem herm_mulVec_of_conjTranspose_mul_H_mul_eq {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H)
    (v w : Fin n → ℂ) : herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frame_move {z e : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) {m : ℕ}
    {F : Fin m → Fin (2 * r + k + 1) → ℂ} (hF : IsFrameOf k r [z, e] F) :
    IsFrameOf k r [z, e] (fun p => h *ᵥ F p) := by
  have hG : h ∈ Glev k r (Fin.last r) := ⟨hh.1, fun a _ => hh.2.1 a⟩
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  refine ⟨fun a => (Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_inWb hG (hF.1 a)).1, fun a b => ?_, fun a v hv => ?_⟩
  · rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]
    exact hF.2.1 a b
  · have hv' : h *ᵥ v = v := by
      rcases List.mem_cons.1 hv with rfl | hv2
      · exact hh.2.2
      · rcases List.mem_cons.1 hv2 with rfl | hv3
        · exact he
        · simp at hv3
    calc herm (Hpk k r) (h *ᵥ F a) v = herm (Hpk k r) (h *ᵥ F a) (h *ᵥ v) := by rw [hv']
      _ = 0 := by rw [herm_mulVec_of_conjTranspose_mul_H_mul_eq hU]; exact hF.2.2 a v hv

theorem frame_swap {z e : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {F : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameOf k r [z, e] F) : IsFrameOf k r [e, z] F :=
  ⟨hF.1, hF.2.1, fun a v hv => hF.2.2 a v (by simp only [List.mem_cons] at hv ⊢; tauto)⟩

private theorem isUnit_det_of_mem_UWset {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) :
    IsUnit h.det := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have h2 := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
  rw [h0, mul_zero] at h2
  exact h2.symm

theorem mulVec_inv_cancel {h : Mx k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    h *ᵥ (h⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

theorem inv_fix {h : Mx k r} {z e : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (he : h *ᵥ e = e) :
    h⁻¹ *ᵥ e = e := by
  calc h⁻¹ *ᵥ e = h⁻¹ *ᵥ (h *ᵥ e) := by rw [he]
    _ = e := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_UWset hh), Matrix.one_mulVec]

end EigenvectorOrthogonality

open EigenvectorOrthogonality in
theorem eigenvector_orthogonality_holds : EigOrth := by
  intro Wp _ _ _ k r z e π hz hT hrep hunit hex f g x y hx hy hfg
  obtain ⟨Fr₀, hFr₀⟩ := hex
  obtain ⟨w₀, hw₀⟩ := hfg
  have hlin : ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr → ∀ w,
      P.Qx8.IsLin (capRep k r π Fr w) := fun Fr hFr w =>
    P.Qx8.capRep_lin hFr (by simp) hrep.1 hrep.2 w
  set S := K k r z e π g with hS

  have hmem : ∀ v ∈ S, v ∈ Kset k r z e π g := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu => exact hu
    | zero =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_zero, smul_zero]
    | add a b _ _ ha hb =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_add a b, ha Fr hFr w, hb Fr hFr w, smul_add]
    | smul c a _ ha =>
      intro Fr hFr w
      rw [(hlin Fr hFr w).map_smul, ha Fr hFr w, smul_comm]

  have hmul : ∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, ∀ v, π (a * b) v = π a (π b v) := by
    intro a ha b hb v
    rw [hrep.1.2 a ha b hb]; rfl
  have hinv : ∀ h ∈ UWset k r z, ∀ v, π h (π h⁻¹ v) = v := by
    intro h hh v
    rw [← hmul h hh _ (WeylGroupFacts.uw_inv hh), Matrix.mul_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1), hrep.1.1]; rfl
  have hstab : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ Kset k r z e π g, π h v ∈ Kset k r z e π g := by
    intro h hh he v hv Fr hFr w
    have hFr' : IsFrameOf k r [z, e] (fun p => h⁻¹ *ᵥ Fr p) := frame_move (WeylGroupFacts.uw_inv hh) (inv_fix hh he) hFr
    have key := P.Qx8.capRep_intertwine (frame_swap hFr') hrep.1 hrep.2 hh.1 (π h)
      (fun h' hh' _ v => by
        rw [← hmul h hh h' hh', ← hmul _ (WeylGroupFacts.uw_mul (WeylGroupFacts.uw_mul hh hh') (WeylGroupFacts.uw_inv hh)) h hh,
          Matrix.mul_assoc (h * h'), Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.mul_one]) w v
    simp only [mulVec_inv_cancel hh] at key
    rw [← key, hv _ hFr' w, map_smul]
  have hstabS : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v ∈ S, π h v ∈ S := fun h hh he v hv =>
    Submodule.subset_span (hstab h hh he v (hmem v hv))
  have hstabO : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ u ∈ Sᗮ, π h u ∈ Sᗮ := by
    intro h hh he u hu s hs
    let L : Wp →ₗᵢ[ℂ] Wp := ⟨(π h : Wp →ₗ[ℂ] Wp), hunit h hh⟩
    have hs' : π h⁻¹ s ∈ S := hstabS _ (WeylGroupFacts.uw_inv hh) (inv_fix hh he) s hs
    have e2 : inner ℂ (π h (π h⁻¹ s)) (π h u) = inner ℂ (π h⁻¹ s) u := L.inner_map_map _ _
    rw [hinv h hh s] at e2
    rw [e2]
    exact Submodule.inner_right_of_mem_orthogonal hs' hu
  have hcomm : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, S.starProjection (π h v) = π h (S.starProjection v) := by
    intro h hh he v
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hstabS h hh he _ (S.starProjection_apply_mem v)) ?_
    intro s hs
    have : π h v - π h (S.starProjection v) = π h (v - S.starProjection v) := by rw [map_sub]
    rw [this]
    exact Submodule.inner_left_of_mem_orthogonal hs
      (hstabO h hh he _ (Submodule.sub_starProjection_mem_orthogonal v))
  have hcap : ∀ v, S.starProjection (capRep k r π Fr₀ w₀ v) = capRep k r π Fr₀ w₀ (S.starProjection v) := by
    intro v
    have key := P.Qx8.capRep_intertwine (frame_swap hFr₀) hrep.1 hrep.2 WeylGroupFacts.uh_one
      (S.starProjection : Wp →L[ℂ] Wp) (fun h' hh' he' v => by
        rw [inv_one, Matrix.one_mul, Matrix.mul_one]; exact hcomm h' hh' he' v) w₀ v
    simpa only [Matrix.one_mulVec] using key
  have hAx : S.starProjection x = 0 := by
    have h1 := hmem _ (S.starProjection_apply_mem x) Fr₀ hFr₀ w₀
    rw [← hcap, hx Fr₀ hFr₀ w₀, map_smul] at h1
    have h2 : (f w₀ - g w₀) • S.starProjection x = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hw₀)
  have hyS : y ∈ S := Submodule.subset_span hy
  rw [← (Submodule.starProjection_eq_self_iff).2 hyS, ← Submodule.inner_starProjection_left_eq_right, hAx, inner_zero_left]

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThConst
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC

noncomputable section

def PolyRadial : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ (n : ℕ) (q : Polynomial ℂ), ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        (((Complex.normSq ζ - P.TT : ℝ) : ℂ) ^ n) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf) =
          q.eval ((Complex.normSq ζ : ℝ) : ℂ) • (Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf)

def ModConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ S, IsSSPt P Bs d l S →
    ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ Bw Bw' : Fin P.k → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [Bs.z] Bw → Q.IsFrameOf P.k P.r [Bs.z'] Bw' →
    ∀ π ρ : M.Ty P, M.Up P l π ρ → ∃ c₁ c₂ : ℝ, ∀ ζ ∈ Gauge.GC.Ann P,
      ∀ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
        (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf →
        ‖B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp (S ζ Xf))‖ ^ 2 = c₁ * ‖B.hsVec Xf‖ ^ 2 ∧
        ‖B.hsVec ((Pr ρ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp
            (tht P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bw Bw' (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)
              (SSn.nu0' P.k P.r Bs.z Bs.z' Bs.μsec ζ) (SSn.io0 P.k P.r Bs.z Bs.z' Bs.μsec ζ) Xf))‖ ^ 2 =
          c₂ * ‖B.hsVec Xf‖ ^ 2

def LineNonzero : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ Pr, PRho.PRhoSpec P Bs.z Bs.π Pr →
    ∀ (π : M.Ty P), ∀ ζ ∈ Gauge.GC.Ann P, ∃ Xf ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      (Pr π (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp Xf = Xf ∧ Xf ≠ 0

def PolyFinish : Prop :=
  ∀ (q : Polynomial ℂ) (n : ℕ) (a C : ℝ),
    (∀ x : ℝ, a < x → Complex.normSq (q.eval (x : ℂ)) = C * (x - a) ^ (2 * n)) →
    ∃ c : ℂ, q = Polynomial.C c * (Polynomial.X - Polynomial.C (a : ℂ)) ^ n

def ThConstOfCut : Prop := PolyRadial → ModConst → LineNonzero → PolyFinish → ThConst

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC
end

