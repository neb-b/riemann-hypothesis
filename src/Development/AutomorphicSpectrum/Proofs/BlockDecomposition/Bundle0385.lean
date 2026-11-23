module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleSplitSndDiagonal
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT bc UJ)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ClassFin

section Reduction

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem projFin_ratEmb_val (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) :
    (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J γ)).1 = bc (inclR (Af F)) γ.1 := by
  refine Units.ext (Matrix.ext fun r s => ?_)
  change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (γ.1.1 r s)) =
    (1 : Af F) ⊗ₜ[F] (γ.1.1 r s)
  simp

end Reduction

section Lattices

open GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume Module
open scoped Pointwise

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

end Lattices

end GlobalTheory.CompanionTheory.ClassFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectors
section
noncomputable section

open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho

namespace GlobalTheory.CompanionTheory.PresRho

theorem eq_zero_of_sum_weightVec {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) (s : Finset ι) :
    ∀ v : ι → A, (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) → ∑ i ∈ s, v i = 0 →
      ∀ i ∈ s, v i = 0 :=
  _root_.UpperTheory.Reformulated.B.P6.r14a.GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec T f hf s

def wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : U n :=
  ∑ m ∈ (pbw.repr x).support.filter (fun m => wt m = w), pbw.repr x m • canon m

theorem isAdW_wtPart {n : ℕ} (x : U n) (w : Fin n → ℤ) : IsAdW w (wtPart x w) := by
  intro k
  simp only [wtPart, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, e_diag_mul_canon_sub,
    (Finset.mem_filter.1 hm).2, smul_comm]

theorem sum_wtPart {n : ℕ} (x : U n) :
    ∑ w ∈ (pbw.repr x).support.image wt, wtPart x w = x := by
  simp only [wtPart]
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact sum_repr_canon x

theorem mem_span_isAdW_of_kills {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (x : U n) (hx : φ x t = 0) :
    x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  classical
  have hinj : Function.Injective (fun (w : Fin n → ℤ) (k : Fin n) => rhoVec n k + (w k : ℂ)) := by
    intro w w' h
    funext k
    have := congrFun h k
    simpa using this
  have hz := eq_zero_of_sum_weightVec (fun k : Fin n => φ (e (k, k)))
    (fun (w : Fin n → ℤ) k => rhoVec n k + (w k : ℂ)) hinj ((pbw.repr x).support.image wt)
    (fun w => φ (wtPart x w) t)
    (fun w _ k => by
      have h1 : e (k, k) * wtPart x w = wtPart x w * e (k, k) + (w k : ℂ) • wtPart x w := by
        rw [← isAdW_wtPart x w k]; abel
      have h2 := congrArg (fun u => φ u t) h1
      simp only [map_mul, map_add (f := _), map_smul, Module.End.mul_apply, LinearMap.add_apply,
        LinearMap.smul_apply, hd k, add_smul] at h2 ⊢
      rw [h2])
    (by
      have h3 := congrArg (fun u => φ u t) (sum_wtPart x)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.sum_apply] at h3
      rw [h3, hx])
  rw [← sum_wtPart x]
  exact Submodule.sum_mem _ fun w hw => Submodule.subset_span ⟨w, isAdW_wtPart x w, hz w hw⟩

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

section Abstract

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

def AvgVanish (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ) (p : G) : Prop :=
  ∃ (L : Subgroup G) (hL : L ≤ U), IsCompact (L : Set G) ∧ ∃ g : cIndSpace H σ,
    f - g ∈ twKer (cInd H σ) L (θ.comp (Subgroup.inclusion hL)) ∧
    (∀ l : L, cInd H σ (l : G) g = ((θ (Subgroup.inclusion hL l) : ℂˣ) : ℂ) • g) ∧
    ∀ u ∈ U, (g : smoothPart (ind H σ)).1.1 (p * u) = 0

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def piPerm (i t : ℕ) : Equiv.Perm (Fin ((i + 1) + t + 1)) :=
  (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)).trans ((ePG i (t + 1)).symm.trans (eGP (i + 1) t))


variable (k) in
def wGL (i t : ℕ) : GL (Fin ((i + 1) + t + 1)) k where
  val := Equiv.Perm.permMatrix k (piPerm i t)⁻¹
  inv := Equiv.Perm.permMatrix k (piPerm i t)
  val_inv := by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]


variable (k) in
def wEl (i t : ℕ) : Mir k ((i + 1) + t + 1) := levi k _ (wGL k i t)


variable (k) in
def sEmb (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype


variable (k) in
def dEmb (i t : ℕ) (d : Fin (t + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) d)), MirU_le_Mir k _ ⟨_, rfl⟩⟩


variable (k) in
def Cl (i t : ℕ) : Set (Mir k ((i + 1) + t + 1)) :=
  {p | ∀ c : Fin (i + 1), (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0}


variable (k) in
def castM {a b : ℕ} (h : a = b) : Mir k a ≃* Mir k b := h ▸ MulEquiv.refl _

section Fibre

variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

abbrev sigX : Representation ℂ (HPG k (i + 1) (t + 1)) (τ.V ⊗[ℂ] σ.V) :=
  (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k (i + 1) (t + 1))

abbrev XS : Submodule ℂ (smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))) := cIndSpace (HPG k (i + 1) (t + 1)) (sigX τ σ)

abbrev evX {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (p : Mir k ((i + 1) + (t + 1))) : τ.V ⊗[ℂ] σ.V :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.1 p

abbrev sigC : Representation ℂ (MirabolicParabolic k (i + 1) t) ((psiN τ).V ⊗[ℂ] σ.V) :=
  (extTensor ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k (i + 1) t)

abbrev sigO (ψ : AddChar k Circle) : Representation ℂ (HPG k i (t + 1)) ((phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (t + 1))

def qC : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (psiN τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ

def qO (ψ : AddChar k Circle) : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ


variable (k) in
def muD (t : ℕ) : @MeasureTheory.Measure (Fin t → k) (borel _) :=
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  MeasureTheory.Measure.addHaar

def intC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
    (fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y))

def intO {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => evX f (dEmb k i t d * y))

def eC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    (psiN τ).V ⊗[ℂ] σ.V :=
  ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m))

def eO (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    (phiN ψ τ).V ⊗[ℂ] σ.V :=
  ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
    qO τ σ ψ (intO f (wEl k i t * sEmb k _ (castM k (by omega) m)))

end Fibre

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BracketWedgeFormula
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.TorC

open CompanionTheory.D.LK (Pos)

section Abstract

variable {R ι : Type*} [Ring R] [Algebra ℂ R] [Fintype ι] [DecidableEq ι]

def br (x y : R) : R := x * y - y * x

theorem br_mul (x y z : R) : br x (y * z) = br x y * z + y * br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_sub, sub_mul, mul_assoc]
  abel

theorem br_add_right (x y z : R) : br x (y + z) = br x y + br x z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_add_left (x y z : R) : br (x + y) z = br x z + br y z := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_add, add_mul]
  abel

theorem br_smul_right (r : ℂ) (x y : R) : br x (r • y) = r • br x y := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, mul_smul_comm, smul_mul_assoc, smul_sub]

theorem br_sum_right {κ : Type*} (s : Finset κ) (x : R) (f : κ → R) : br x (∑ i ∈ s, f i) = ∑ i ∈ s, br x (f i) := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]

theorem br_anti (x y : R) : br x y = -br y x := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.br, neg_sub]

theorem swap3 {M : Type*} [AddCommMonoid M] (g : ι → ι → ι → M) :
    ∑ j, ∑ k, ∑ b, g j k b = ∑ b, ∑ k, ∑ j, g j k b := by
  calc ∑ j, ∑ k, ∑ b, g j k b = ∑ j, ∑ b, ∑ k, g j k b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, g j k b := Finset.sum_comm
    _ = ∑ b, ∑ k, ∑ j, g j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem swap4 {M : Type*} [AddCommMonoid M] (f : ι → ι → ι → ι → M) :
    ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b := by
  calc ∑ i, ∑ j, ∑ k, ∑ b, f i j k b = ∑ i, ∑ j, ∑ b, ∑ k, f i j k b :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ b, ∑ j, ∑ k, f i j k b := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ b, ∑ i, ∑ j, ∑ k, f i j k b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ i, ∑ k, f i j k b := Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ i, f i j k b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

def Dm (a c : ι → R) (A : ι → ι → ℂ) : R := ∑ i, ∑ k, A i k • (c k * a i)

theorem reindex (W : ι → ι → ι → R) (S : ι → ι → ι → ℂ) (A : ι → ι → ℂ) :
    ∑ i, ∑ j, ∑ k, S i j k • ((∑ l, A k l • W i j l) - (∑ b, A b j • W i b k) - ∑ b, A b i • W b j k) =
      ∑ i, ∑ j, ∑ k, ((∑ m, S i j m * A m k) - (∑ m, S i m k * A j m) - ∑ m, S m j k * A i m) • W i j k := by
  simp only [smul_sub, sub_smul, Finset.smul_sum, Finset.sum_smul, smul_smul, Finset.sum_sub_distrib]
  refine congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  · exact Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.RealMult.TorC.swap3 _
  · exact GlobalTheory.CompanionTheory.RealMult.TorC.swap4 _

variable {a c : ι → R}

theorem term_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (a m) = -(if m = k then a i else 0) := by
  have h₁ : a i * a m = -(a m * a i) := eq_neg_of_add_eq_zero_left (haa i m)
  have h₂ : a m * c k = (if m = k then 1 else 0) - c k * a m := eq_sub_of_add_eq (hac m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (a m), h₂]
  split_ifs <;> simp only [sub_mul, mul_neg, mul_assoc, one_mul, zero_mul] <;> abel

theorem term_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (i k m : ι) :
    br (c k * a i) (c m) = if i = m then c k else 0 := by
  have h₁ : a i * c m = (if i = m then 1 else 0) - c m * a i := eq_sub_of_add_eq (hac i m)
  have h₂ : c m * c k = -(c k * c m) := eq_neg_of_add_eq_zero_left (hcc m k)
  unfold GlobalTheory.CompanionTheory.RealMult.TorC.br
  rw [mul_assoc, h₁, ← mul_assoc (c m), h₂]
  split_ifs <;> simp only [mul_sub, neg_mul, mul_assoc, mul_one, mul_zero] <;> abel

theorem dm_a (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (a m) = -∑ i, A i m • a i := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (a m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (a m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • -(if m = k then a i else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_a haa hac]
    _ = -∑ i, A i m • a i := by
          simp [smul_ite, Finset.sum_neg_distrib]

theorem dm_c (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (m : ι) :
    br (Dm a c A) (c m) = ∑ k, A m k • c k := by
  calc GlobalTheory.CompanionTheory.RealMult.TorC.br (GlobalTheory.CompanionTheory.RealMult.TorC.Dm a c A) (c m)
        = ∑ i, ∑ k, A i k • GlobalTheory.CompanionTheory.RealMult.TorC.br (c k * a i) (c m) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br,
            Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_sub,
            Finset.sum_sub_distrib]
    _ = ∑ i, ∑ k, A i k • (if i = m then c k else 0) := by
          simp only [GlobalTheory.CompanionTheory.RealMult.TorC.term_c hcc hac]
    _ = ∑ k, A m k • c k := by
          rw [Finset.sum_comm]
          simp [smul_ite]

theorem bracket_wedge_formula (haa : ∀ i j, a i * a j + a j * a i = 0) (hcc : ∀ i j, c i * c j + c j * c i = 0)
    (hac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (A : ι → ι → ℂ) (i j k : ι) :
    br (Dm a c A) (c k * a j * a i) =
      (∑ l, A k l • (c l * a j * a i)) - (∑ b, A b j • (c k * a b * a i)) - ∑ b, A b i • (c k * a j * a b) := by
  rw [GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_c hcc hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac,
    GlobalTheory.CompanionTheory.RealMult.TorC.dm_a haa hac]
  simp only [add_mul, mul_neg, neg_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, mul_assoc]
  abel

theorem br_lift_dm {L : R} (hLa : ∀ i, br L (a i) = 0) (hLc : ∀ i, br L (c i) = 0) (A : ι → ι → ℂ) :
    br L (Dm a c A) = 0 := by
  simp only [GlobalTheory.CompanionTheory.RealMult.TorC.Dm, GlobalTheory.CompanionTheory.RealMult.TorC.br_sum_right,
    GlobalTheory.CompanionTheory.RealMult.TorC.br_smul_right, GlobalTheory.CompanionTheory.RealMult.TorC.br_mul, hLa, hLc, zero_mul, mul_zero,
    add_zero, smul_zero, Finset.sum_const_zero]

end Abstract

section Car

variable {n : ℕ}

theorem key_lt (p : Pos n) : CompanionTheory.D.LK.key p < n * n := by
  unfold CompanionTheory.D.LK.key
  have h1 := p.1.1.2
  have h2 := p.1.2.2
  nlinarith

theorem keyR_inj {i j : Ix n} (h : keyR i = keyR j) : i = j := by
  obtain ⟨b, p⟩ := i
  obtain ⟨b', q⟩ := j
  have hp := key_lt p
  have hq := key_lt q
  cases b <;> cases b' <;> simp only [keyR, if_true, Bool.false_eq_true, if_false] at h
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]
  · omega
  · omega
  · rw [CompanionTheory.D.LK.Car.key_inj (by omega : CompanionTheory.D.LK.key p = CompanionTheory.D.LK.key q)]

def tw (i j : Ix n) : ℂ := if keyR j < keyR i then -1 else 1

theorem tw_self (i : Ix n) : tw i i = 1 := by simp [tw]

theorem tw_mul_self (i j : Ix n) : tw i j * tw i j = 1 := by
  unfold tw; split_ifs <;> simp

theorem tw_swap {i j : Ix n} (h : i ≠ j) : tw j i = -tw i j := by
  have hk : keyR i ≠ keyR j := fun e => h (keyR_inj e)
  unfold tw
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem liftR_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cr n V)
    (A : Finset (Ix n)) : liftR n T x A = T (x A) := rfl

theorem br_lift_lift (T S : Module.End ℂ V) :
    br (liftR n T : Module.End ℂ (Cr n V)) (liftR n S) = liftR n (br T S) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp [br, liftR_apply]

end Car

section Coefficients

variable {n : ℕ}

end Coefficients

section Units

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

variable {E1 E2 : Fin n → Fin n → Module.End ℂ V}

end Units

end GlobalTheory.CompanionTheory.RealMult.TorC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapPNeg
section
namespace GlobalTheory.CompanionTheory.PairMult

theorem capelliPoly_neg {n : ℕ} (χ : Fin n → ℂ) (Y : ℂ) :
    Formalism.QuantumDeterminants.capP (fun a => -χ a) (-Y) = (-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y := by
  have h : ∀ s : Fin n, -Y + -χ s = (-1 : ℂ) * (Y + χ s) := fun s => by ring
  simp only [Formalism.QuantumDeterminants.capP, h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.CompanionTheory.PairMult
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSumStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_levi_factorization_sum : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (r + s)), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → ∀ m : GA E r × GA E s, (cap (a := r + s) τ u F).1 (lev (Ad E) r s m) = (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) F)).1 (lev (Ad E) r s m) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi | exact GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi | (intros; apply GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPowStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_norm_eq_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  first | exact @GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow | exact GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow | (intros; apply GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSupportRealisedByProduct
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenSupp

theorem hasSupport_std : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL (k := k))), HasSupport π s → ∃ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Finset.univ.val.map x = s ∧ (∀ a, (x a).IsCusp) ∧ IsSubquotient π (prodIrr x hd) := by
  intro k _ _ _ _ N V _ _ π s hπ
  obtain ⟨h, x, hs, -, hc, e, hsq⟩ := hπ
  have hd : ∑ a, (x a).1 = N := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sigma] using this
  obtain ⟨φ⟩ := _root_.GlobalTheory.CompanionTheory.GenMultiProd.multiProd_equiv_stdBlocks k (fun a => (x a).1) hd e _ (fun a => (x a).rep)
  exact ⟨h, x, hd, hs, fun a => ⟨(hc a).1, (hc a).2.2⟩, hsq.trans (GlobalTheory.JacStages.isSubquotient_of_equiv φ)⟩

end GlobalTheory.CompanionTheory.GenSupp
end

