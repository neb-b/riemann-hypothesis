module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianSideClassesEqFormClasses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

section GenP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open scoped TensorProduct

theorem val_nat_lt_one (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (h : (g : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (g : v.adicCompletion F) < 1 := by
  have h1 : v.valuation F (algebraMap (𝓞 F) F (g : 𝓞 F)) < 1 := (v.valuation_lt_one_iff_mem _).2 h
  have h2 : ((g : v.adicCompletion F)) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F)) := by
    simp only [map_natCast]
  rw [h2]
  exact lt_of_eq_of_lt (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (g : 𝓞 F))) h1

theorem redM_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : v.adicCompletion F) (hg : Valued.v g < 1)
    (X W : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hW : ∀ a b, W a b ∈ v.adicCompletionIntegers F)
    (hX : ∀ a b, X a b = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b + g * W a b) :
    redM F v X = 1 := by
  have hgi : g ∈ v.adicCompletionIntegers F := le_of_lt hg
  have h1 : ∀ a b, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F := by
    intro a b
    by_cases e : a = b
    · subst e
      rw [Matrix.one_apply_eq]
      exact one_mem _
    · rw [Matrix.one_apply_ne e]
      exact zero_mem _
  ext a b
  have hm : X a b ∈ v.adicCompletionIntegers F := by
    rw [hX]
    exact add_mem (h1 a b) (mul_mem hgi (hW a b))
  have hz : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨g, hgi⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (Valuation.integer.integers (Valued.v (R := v.adicCompletion F))).isUnit_iff_valuation_eq_one.1 hu
    exact absurd this (ne_of_lt hg)
  have e : (⟨X a b, hm⟩ : v.adicCompletionIntegers F) =
      ⟨(1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b, h1 a b⟩ + ⟨g, hgi⟩ * ⟨W a b, hW a b⟩ := by
    exact Subtype.ext ((hX a b).trans rfl)
  simp only [redM]
  rw [dite_eq_left hm, e, map_add (f := _), map_mul, hz, zero_mul, add_zero]
  by_cases ab : a = b
  · subst ab
    simp only [Matrix.one_apply_eq]
    exact map_one _
  · simp only [Matrix.one_apply_ne ab]
    exact map_zero _

theorem mem_Uloc_of_princ {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ}
    {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ} (S : StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH S G H lam)
    (hLb : ∀ b : Fin n, (Pi.single b 1 : Fin n → E) ∈ S.Lb)
    (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (hfr : V.fr i v h = 1)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hx : x ∈ levelVL σ J v S.Lb)
    (hc : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
      ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) :
    x ∈ S.Uloc v := by
  have hint : ∀ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      G.phi i v h (z a) ∈ v.adicCompletionIntegers F := by
    intro z hz a
    have := (V.fr_lat i v h (fun b => G.phi i v h (z b))).1 ⟨z, hz, fun _ => rfl⟩ a
    rw [hfr] at this
    simpa using this
  have hcol : ∀ b : Fin n, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∀ a,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + (gp i : E ⊗[F] v.adicCompletion F) * z a := by
    intro b
    have e1 : (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single b 1 : Fin n → E) j)) =
        (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) := by
      funext j
      by_cases e : j = b
      · subst e
        simp
      · simp [e]
    have hb : (Pi.single b 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
      rw [← e1]
      exact Submodule.subset_span ⟨_, hLb b, rfl⟩
    obtain ⟨z, hz, e⟩ := hc _ hb
    refine ⟨z, hz, fun a => ?_⟩
    have := congrFun e a
    rw [Matrix.mulVec_single_one] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
    rw [← this]
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  choose Z hZ hZe using hcol
  refine (V.mem i v h x hx).2 ⟨1, one_mem _, ?_⟩
  have key : redM F v (G.mat i v h (V.fr i v h) x) = 1 := by
    rw [hfr]
    refine redM_eq_one v (gp i : v.adicCompletion F) (val_nat_lt_one v (gp i) h) _
      (fun a b => G.phi i v h (Z b a)) (fun a b => hint _ (hZ b) a) fun a b => ?_
    have e2 : G.mat i v h 1 x a b = G.phi i v h ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) := by
      simp [GLoc.mat, bc]
    rw [e2, hZe b a, map_add (f := _), map_mul, map_natCast]
    congr 1
    by_cases ab : a = b
    · subst ab
      simp
    · simp [ab]
  rw [key]
  rfl

end GenP

section Tr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_rfl_apply {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_rfl_hom {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_rfl_apply R g

theorem reL_rfl {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem co_rfl (S : HSpace E) : co S rfl = Formalism.L2.Herm.crd S :=
  LinearEquiv.ext fun x => funext fun j => by simp [co, Formalism.L2.Herm.crd]

theorem tie_of_forms (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (hO : Crd.Ortho S)
    {σ : E →ₐ[F] E} (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    {f : ℕ} {gp : Fin 2 → ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (hbad : bad = {v | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal})
    (St : StepLevel F E σ J 1 f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (V : GLevH St G H lam) (hfr : ∀ a v h, V.fr a v h = 1)
    (hLb : ∀ x, x ∈ St.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 E) E).range)
    {cls : Type} {stab : cls → Type} [∀ c, Group (stab c)]
    (y : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls St)))
    (lat : cls → Submodule (𝓞 E) (Fin n → E))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔
      ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) St.Lb)
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ St.U.map (MulAut.conj (y c).1).toMonoidHom) :
    ∃ (lattice₂ : cls → Submodule (𝓞 E) S.V) (levP : Formalism.L2.Herm.StepLevel0 hc S gp (Formalism.L2.Herm.crdLat S S.L0))
      (clsP : Formalism.L2.Herm.ClassTie hc S (Formalism.L2.Herm.crdLat S S.L0) levP.U stab lattice₂),
      SameCar h (Formalism.L2.Herm.crdLat S S.L0) St.Lb levP.Uloc St.Uloc levP.U St.U
        (fun c => (clsP.y c).1) (fun c => (y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => (stabI c s).1) ∧
      ∀ c, lat c = (lattice₂ c).map (((co S h : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := hJ.trans (by ext a b; simp)
  subst hbad
  have hL : St.Lb = Formalism.L2.Herm.crdLat S S.L0 := by
    ext x
    rw [hLb x, ← hO.mem_standardLattice_iff_integral_coords rfl x]
    unfold Formalism.L2.Herm.crdLat
    rw [show Crd.co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
  have hone : ∀ v : HeightOneSpectrum (𝓞 F), ((1 : ℕ) : 𝓞 F) ∉ v.asIdeal := fun v hv =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using hv))
  have hs : ∀ b : Fin S.rank, (Pi.single b 1 : Fin S.rank → E) ∈ St.Lb := by
    intro b
    refine (hLb _).2 fun j => ?_
    by_cases e : j = b
    · subst e
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [e]⟩
  refine ⟨fun c => (lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E)),
    { Uloc := St.Uloc
      Uloc_lev := fun v => hL ▸ St.Uloc_lev v
      Uloc_hyp := fun v h0 h1 => ?_
      Uloc_g := fun i v hv x hx => ?_
      U := St.U
      U_eq := St.U_eq },
    { y := y
      y_bij := y_bij
      y_lat := fun c x => ?_
      stabI := stabI
      stabI_inj := stabI_inj
      stabI_range := stabI_range }, ⟨?_, fun v => ?_, ?_, fun c => ?_, fun c s => ?_⟩, fun c => ?_⟩
  · rw [St.Uloc_hyp v (by rintro (h | h); exacts [h0 h, h1 h]) (hone v), hL]
  · rw [← hL] at hx
    exact mem_Uloc_of_princ St G V hs i v hv (hfr i v hv) x hx.1 hx.2
  · have e : Formalism.L2.Herm.crdLat S ((lat c).map (((Formalism.L2.Herm.crd S).symm : (Fin S.rank → E) →ₗ[E] S.V).restrictScalars (𝓞 E))) = lat c :=
      Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)
    rw [e, ← hL]
    exact y_lat c x
  · rw [reL_rfl, hL]
  · show St.Uloc v = (St.Uloc v).map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · show St.U = St.U.map (reGL rfl _).toMonoidHom
    rw [reGL_rfl_hom, Subgroup.map_id]
  · exact (reGL_rfl_apply _ _).symm
  · exact (reGL_rfl_apply _ _).symm
  · rw [show co S rfl = Formalism.L2.Herm.crd S from co_rfl S]
    exact (Crd.map_symm_map (Formalism.L2.Herm.crd S) (lat c)).symm

end Tr


set_option maxHeartbeats 4000000 in
theorem clsP_hermitian : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, ∃ (lattice₂ : ((I.rec7 l Z).fm u).clsP → Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).sp.X'.V) (levP : Formalism.L2.Herm.StepLevel0 (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (I.rec7 l Z).host.g (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0)) (clsP : Formalism.L2.Herm.ClassTie (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) levP.U ((I.rec7 l Z).fm u).stabilizer₂ lattice₂), SameCar (rankP (I.rec7 l Z)) (Formalism.L2.Herm.crdLat (I.rec7 l Z).sp.X' (I.rec7 l Z).sp.X'.L0) (F u).clsP.lev.Lb levP.Uloc (F u).clsP.lev.Uloc levP.U (F u).clsP.lev.U (fun c => (clsP.y c).1) (fun c => ((F u).clsP.y c).1) (fun c s => (clsP.stabI c s).1) (fun c s => ((F u).clsP.stabI c s).1) ∧ ∀ c, (F u).clsP.lat c = (lattice₂ c).map ((crdP (I.rec7 l Z) : (I.rec7 l Z).sp.X'.V →ₗ[(I.rec7 l Z).host.E] (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) → (I.rec7 l Z).host.E)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) := by
  intro B X I hI hP l Z H F hstd hcar u
  obtain ⟨hs, -, hX', -⟩ := hI.spaces
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  have hr := (hstd u).1.what₂
  have hLb : ∀ x, x ∈ (F u).clsP.lev.Lb ↔ ∀ j, x j ∈ (algebraMap (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E).range := by
    intro x
    refine (hr.lb x).trans ⟨fun hx j => ?_, fun hx j => ?_⟩
    · obtain ⟨r, e, -⟩ := hx j
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e⟩ := hx j
      exact ⟨r, e.symm, fun _ => one_dvd r⟩
  exact tie_of_forms (I.rec7 l Z).sp.cm (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) oX' rfl rfl rfl (F u).clsP.lev (F u).gl
    (F u).glevP (hstd u).1.frP hLb (F u).clsP.y (F u).clsP.y_bij (F u).clsP.lat (F u).clsP.y_lat (F u).clsP.stabI
    (F u).clsP.stabI_inj (F u).clsP.stabI_range

end GlobalTheory.Mem.Col2.HAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaWildOfTrivialTameCharacters
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

namespace GlobalTheory.TameWild

theorem sub_one_lt_one_of_pow {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [hg : Fact g.Prime]
    (hvg : A.valuation (g : Ω) < 1) {z : Ω} (a : ℕ) (hz : A.valuation (z ^ (g ^ a) - 1) < 1) :
    A.valuation (z - 1) < 1 := by
  have hz1 : A.valuation z ≤ 1 := by
    have h : A.valuation (z ^ g ^ a) ≤ 1 := by
      have e : z ^ g ^ a = (z ^ g ^ a - 1) + 1 := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le hz.le (by simp))
    rw [map_pow] at h
    by_contra hc
    push Not at hc
    exact absurd h (not_le.2 (one_lt_pow' hc (pow_ne_zero _ hg.out.ne_zero)))
  have hzA : z ∈ A := (A.valuation_le_one_iff z).1 hz1
  let zA : A := ⟨z, hzA⟩
  haveI : CharP (IsLocalRing.ResidueField A) g := by
    rw [CharP.charP_iff_prime_eq_zero hg.out, ← map_natCast (IsLocalRing.residue A),
      IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hvg
  have h1 : IsLocalRing.residue A (zA ^ g ^ a - 1) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa [zA] using hz
  have h2 : IsLocalRing.residue A (zA - 1) = 0 := by
    apply pow_eq_zero_iff (n := g ^ a) (pow_ne_zero _ hg.out.ne_zero) |>.1
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, ← map_one (IsLocalRing.residue A), ← map_sub, h1]
  rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h2
  simpa [zA] using h2


open GlobalTheory.TameInertiaGen in
theorem cob_lt_one_of_tame : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ τ ∈ Ine (F := E) A, (∀ d, 0 < d → ∃ y : Ω, y ^ (g ^ d - 1) = ((g : ℕ) : Ω) ∧ A.valuation (τ y / y - 1) < 1) → ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv τ hτ hroot y hy
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this
  obtain ⟨p, hp0, hp⟩ := exists_nat_gen A
  have halg : IsAlgebraic ℤ y := by
    have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, k, hm, hk⟩ := exists_pow_eq A hp0 hp hy halg
  obtain ⟨e, he⟩ := hp g hg.out.ne_zero
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [he, pow_zero] at hvg
    exact lt_irrefl _ hvg
  have hM0 : m * e ≠ 0 := mul_ne_zero hm he0
  have hM : A.valuation y ^ (m * e) = A.valuation (g : Ω) ^ k := by
    rw [pow_mul, hk, he, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  obtain ⟨a, m', hm', hM'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM0 g hg.out.ne_one
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hm' (dvd_zero _)
  set d := m'.totient with hd
  have hdpos : 0 < d := Nat.totient_pos.2 (Nat.pos_of_ne_zero hm'0)
  have hcop : g.Coprime m' := (Nat.Prime.coprime_iff_not_dvd hg.out).2 hm'
  have hdvd : m' ∣ g ^ d - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hg.out.pos)).1 (Nat.ModEq.pow_totient hcop).symm
  obtain ⟨c, hc⟩ := hdvd
  obtain ⟨r, hr, hrτ⟩ := hroot d hdpos
  have hN : g ^ d - 1 ≠ 0 := by
    have := Nat.one_lt_pow hdpos.ne' hg.out.one_lt
    omega
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hr
    exact hg.out.ne_zero (by exact_mod_cast hr.symm)
  have hR : cob τ (Units.mk0 r hr0) ∈ A.principalUnitGroup := by
    rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob, Units.val_mk0]
    exact hrτ
  have hval : A.valuation ((Units.mk0 (y ^ g ^ a) (pow_ne_zero _ hy) : Ωˣ) : Ω) =
      A.valuation ((Units.mk0 r hr0 : Ωˣ) : Ω) ^ ((c : ℤ) * k) := by
    rw [Units.val_mk0, Units.val_mk0, ← pow_left_inj₀ zero_le zero_le hm'0, map_pow, ← pow_mul, ← hM', hM, ← hr,
      map_pow, hc, ← zpow_natCast (A.valuation r) (m' * c),
      ← zpow_natCast (A.valuation r ^ ((c : ℤ) * k)) m', ← zpow_mul, ← zpow_mul]
    congr 1
    push_cast
    ring
  have h1 := cob_mem_of_zpow hτ hR hval
  rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob, Units.val_mk0, map_pow, ← div_pow] at h1
  exact sub_one_lt_one_of_pow A hvg a h1

end GlobalTheory.TameWild
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgClosedResidueField
section
noncomputable section

namespace GlobalTheory.ResidueFieldAlgClosed

open Polynomial

theorem isAlgClosed_residueField {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective p
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hdeg : (P.map (algebraMap A Ω)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, hPdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hint : IsIntegral A α := ⟨P, hPmon, by rw [← Polynomial.eval_map]; exact hα⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have h0 : P.eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]
    exact hα
  refine ⟨IsLocalRing.residue A a, ?_⟩
  rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]

theorem isAlgebraic_residueField {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω)
    (hΩ : ∀ y : Ω, IsAlgebraic ℤ y) (g : ℕ) [Fact g.Prime] [Algebra (ZMod g) (IsLocalRing.ResidueField A)] :
    Algebra.IsAlgebraic (ZMod g) (IsLocalRing.ResidueField A) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨p, hp0, hpa⟩ := hΩ (a : Ω)
  have hc : (p.content : Ω) ≠ 0 := Int.cast_ne_zero.mpr (mt Polynomial.content_eq_zero_iff.mp hp0)
  have hqa : Polynomial.aeval (a : Ω) p.primPart = 0 := by
    rw [Polynomial.eq_C_content_mul_primPart p, map_mul, Polynomial.aeval_C] at hpa
    exact (mul_eq_zero.mp hpa).resolve_left (by simpa using hc)
  have hA0 : Polynomial.aeval a p.primPart = 0 := by
    apply IsFractionRing.injective A Ω
    rw [map_zero]
    calc algebraMap A Ω (Polynomial.aeval a p.primPart)
        = Polynomial.aeval (algebraMap A Ω a) p.primPart :=
          (Polynomial.aeval_algHom_apply (algebraMap A Ω).toIntAlgHom a p.primPart).symm
      _ = 0 := hqa
  have hqg : p.primPart.map (Int.castRingHom (ZMod g)) ≠ 0 := by
    intro h
    have hdvd : Polynomial.C (g : ℤ) ∣ p.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r i) h
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ g).mp hi
    have hu := Polynomial.isPrimitive_primPart p _ hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := (Fact.out : g.Prime).two_le
    omega
  refine ⟨p.primPart.map (Int.castRingHom (ZMod g)), hqg, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a p.primPart
  rw [hA0, map_zero] at h2
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [Polynomial.aeval_def] at h2
  have hφ : (algebraMap (ZMod g) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod g)) =
      algebraMap ℤ (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
  rw [hφ]
  exact h2

theorem residueField_equiv (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (g : ℕ) [Fact (Nat.Prime g)]
    (hg : (g : NumberField.RingOfIntegers E) ∈ v.asIdeal) :
    Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have hΩ : ∀ y : Ω, IsAlgebraic ℤ y := fun y =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  have hg0 : (g : IsLocalRing.ResidueField A) = 0 := by
    have h1 := (hA (g : NumberField.RingOfIntegers E)).mpr hg
    have h2 : A.valuation ((g : A) : Ω) < 1 := by simpa using h1
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact (A.valuation_lt_one_iff (g : A)).mpr h2
  have : CharP (IsLocalRing.ResidueField A) g := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hg0
  let _ : Algebra (ZMod g) (IsLocalRing.ResidueField A) := ZMod.algebra _ g
  have _ := isAlgClosed_residueField A
  have _ := isAlgebraic_residueField A hΩ g
  have : IsAlgClosure (ZMod g) (IsLocalRing.ResidueField A) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod g) (IsLocalRing.ResidueField A) (Formalism.CyclotomicNorms.Fbar g)).toRingEquiv⟩

end GlobalTheory.ResidueFieldAlgClosed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsOfLocMv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def LocMv (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1) : Prop :=
  (I.stp u a i).gam c.1 κ = 1 ∧
    cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
    ∀ g : GA B (B.R.N i), PtOf g ((I.stp u a i).rep c).1.1 → PtOf (g * s) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1

theorem reads_of_locMv (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (κ : (I.stp u a i).G c.1) (h : LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ) :
    ∃ hx : x ∈ U (chOf c), ((chi (chOf c) ⟨x, hx⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hq := h.2.2 _ hp
  rw [e] at hq
  have hx : x ∈ U (chOf c) := (hR.lev c x _ hq).2 ⟨κ, h.1, rfl, h.2.1⟩
  exact ⟨hx, hR.chr c ⟨x, hx⟩ κ h.1 hq⟩

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldEquivRealSubfieldQuotientTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_equiv_realSubfieldQuotient_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ v : ((I.rec7 l Z).mem u).A.vT,
  ∃ e : ((I.rec7 l Z).mem u).A.Fv v ≃+* (𝓞 (I.rec7 l Z).host.F ⧸ (F.atT.eV v).1.asIdeal),
    ∀ a : 𝓞 (I.rec7 l Z).host.F, e (F.atT.res v (algebraMap (𝓞 (I.rec7 l Z).host.F) (𝓞 (I.rec7 l Z).host.E) a)) = Ideal.Quotient.mk _ a := by
  first | exact @GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | exact GlobalTheory.Mem.Col2.ResF.fv_equiv_quot | (intros; apply GlobalTheory.Mem.Col2.ResF.fv_equiv_quot <;> assumption)
end

