module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0245
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0288
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeClosedOfStatement
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
public import Formalism.GelfandTransference.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0383
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosed
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening GroundTheory.Arith.SchemeCoh
namespace GlobalTheory.CompanionTheory.GE

theorem step_integral {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))]
    (J : X.IdealSheafData) [IsIntegral J.subscheme]
    (IH : ∀ J' : X.IdealSheafData, J < J' → Statement I J') : Statement I J := by
  intro E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  letI : J.subscheme.Over (Spec (.of A)) := ⟨J.subschemeι ≫ (X ↘ Spec (.of A))⟩
  have h1 : IsSeparated (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : IsSeparated (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h2 : LocallyOfFiniteType (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : LocallyOfFiniteType (J.subschemeι ≫ (X ↘ Spec (.of A))))
  have h3 : QuasiCompact (J.subscheme ↘ Spec (.of A)) :=
    (inferInstance : QuasiCompact (J.subschemeι ≫ (X ↘ Spec (.of A))))
  obtain ⟨N, Y, i, O, ψ, W, hi, hψ, hcomm, hW, hiso⟩ := _root_.GlobalTheory.CompanionTheory.GE.ChowOpen.exists_chow_open (A := A) (X := J.subscheme)
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ i ≫ ProjSpace.toSpecBase A N⟩
  have hZ : Statement I (⊥ : (O : Scheme.{0}).IdealSheafData) := GlobalTheory.T.formal_existence_projective_open I hI i hi O
  have hover : (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = ((O : Scheme.{0}) ↘ Spec (.of A)) := by
    change (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = O.ι ≫ i ≫ ProjSpace.toSpecBase A N
    rw [hcomm, Category.assoc]
    rfl
  obtain ⟨D, c, J', hDq, hDP, hc, hJ, hkill⟩ := _root_.GlobalTheory.CompanionTheory.GE.core_integral_step I hI J hZ ψ hψ hover W hW hiso hE hS hK hP
  obtain ⟨c', hS', hP', halg⟩ := GlobalTheory.T.artin_rees_closed_system I hE hS hP D hDq c hc
  exact halg (IH J' hJ _ (GlobalTheory.T.coherent_subobject_coherent hE D hDq) _ hS' (GlobalTheory.T.restricted_system_killed_by_ideal I J' D S c' hkill) hP') hDP

theorem statement_bot {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : IsAdicComplete I A)
    (X : Scheme.{0}) [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] :
    Statement I (⊥ : X.IdealSheafData) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hno : IsNoetherian X := ⟨⟩
  have hwf : WellFoundedGT X.IdealSheafData := _root_.GlobalTheory.CompanionTheory.GE.idealSheafData_wellFoundedGT
  refine WellFoundedGT.induction (motive := fun J : X.IdealSheafData => Statement I J) ⊥ ?_
  intro J IH
  by_cases hJ : J = ⊤
  · subst hJ
    exact _root_.GlobalTheory.CompanionTheory.GE.Unit.statement_top I
  rcases _root_.GlobalTheory.CompanionTheory.GE.Dich.isIntegral_or_exists_mul_mem J hJ with h | ⟨J₁, J₂, h₁, h₂, hm⟩
  · exact step_integral I hI J IH
  · exact _root_.GlobalTheory.CompanionTheory.GE.NonPrime.statement_of_mul_mem I J J₁ J₂ hm (IH _ h₁) (IH _ h₂)

theorem geClosed : GEClosed :=
  _root_.GlobalTheory.CompanionTheory.GE.Close.geClosed_of_statement fun _ _ _ I hI X _ _ _ _ => statement_bot I hI X

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosed
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.MirGP

theorem isClosed_HGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  intro k _ _ _ _ m j
  have h := GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (m + j + 1))
    (GlobalTheory.SmGL.Two (Fin m) (Fin (j + 1))) (GlobalTheory.BZMir.Leib.eGP m j)
  exact h.2.2.2.2.2.2.1.preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.MirGP
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtMulVec
section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)
open Formalism.BasicNotions Formalism.GradedWeylDivisibility

namespace GlobalTheory.CompanionTheory.RmHol.HW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def hv (lam : Fin n → ℤ) : nablaSq ℂ n (dw lam) :=
  ⟨extremal ℂ n (dw lam), hwMem ℂ n n le_rfl _ (factNatW n (dw lam)).1⟩

theorem hv_ne (lam : Fin n → ℤ) : hv lam ≠ 0 := fun h =>
  hwNe ℂ n n le_rfl (dw lam).natW (congrArg Subtype.val h)

theorem dw_w {lam : Fin n → ℤ} (h : Antitone lam) (a : Fin n) : (dw lam).w a = lam a := by
  unfold dw
  rw [dite_eq_left h]

theorem Rm_mulVec (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) (v : nablaSq ℂ n (dw lam)) :
    Rm lam x *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
      ((wb lam).repr (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h) v) : Jd n lam → ℂ) := by
  rw [Rm_of_unit lam h]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

theorem hasDerivAt_mulVec {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (c : Jd n lam → ℂ)
    (i : Jd n lam) :
    HasDerivAt (fun t : ℂ => (Rm lam (1 + t • B) *ᵥ c) i) ((XA lam B *ᵥ c) i) 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_line hD B i j).mul_const _

theorem fix_upper (lam : Fin n → ℤ) {a b : Fin n} (hab : a < b) {t : ℂ}
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) = hv lam := by
  apply Subtype.ext
  refine (factSqHighestWeight ℂ n (dw lam)).2 _ ?_ ?_
  · intro i j hij
    have hij' : j < i := hij
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i j = 0
    have h1 : (1 : Mat n) i j = 0 := Matrix.one_apply_ne (ne_of_gt hij')
    have h2 : Matrix.single a b (1 : ℂ) i j = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, rfl⟩
      exact absurd hab (not_lt.2 hij'.le)
    rw [Matrix.add_apply, Matrix.smul_apply, h1, h2]
    simp
  · intro i
    show ((1 : Mat n) + t • Matrix.single a b (1 : ℂ)) i i = 1
    have h2 : Matrix.single a b (1 : ℂ) i i = 0 := by
      rw [Matrix.single_apply_of_ne]
      rintro ⟨rfl, h⟩
      exact hab.ne' h
    rw [Matrix.add_apply, Matrix.smul_apply, h2]
    simp

theorem diag_act {lam : Fin n → ℤ} (hA : Antitone lam) (a : Fin n) {t : ℂ} (ht : 1 + t ≠ 0)
    (h : IsUnit ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)).det) :
    GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit _ h) (hv lam) =
      ((1 + t) ^ (lam a)) • hv lam := by
  classical
  let u : Fin n → ℂˣ := fun i => if i = a then Units.mk0 (1 + t) ht else 1
  have e : Matrix.nonsingInvUnit _ h = diagGL ℂ n u := by
    apply Units.ext
    ext i j
    show ((1 : Mat n) + t • Matrix.single a a (1 : ℂ)) i j = Matrix.diagonal (fun k => (u k : ℂ)) i j
    by_cases hij : i = j
    · subst hij
      by_cases hia : i = a
      · subst hia; simp [u]
      · have h2 : Matrix.single a a (1 : ℂ) i i = 0 := by
          rw [Matrix.single_apply_of_ne]
          rintro ⟨h, -⟩
          exact hia h.symm
        rw [Matrix.add_apply, Matrix.smul_apply, h2]
        simp [u, hia]
    · have h2 : Matrix.single a a (1 : ℂ) i j = 0 := by
        rw [Matrix.single_apply_of_ne]
        rintro ⟨h, h'⟩
        exact hij (h.symm.trans h')
      rw [Matrix.add_apply, Matrix.smul_apply, h2, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
      simp
  have hp : ((∏ i, (u i) ^ ((dw lam).w i) : ℂˣ) : ℂ) = (1 + t) ^ (lam a) := by
    rw [Finset.prod_eq_single a]
    · simp [u, dw_w hA]
    · intro b _ hb
      simp [u, hb]
    · simp
  rw [e]
  apply Subtype.ext
  have hh := (factSqHighestWeight ℂ n (dw lam)).1 u
  rw [hp] at hh
  exact hh

theorem exists_hw (n : ℕ) (lam : Fin n → ℤ) (hD : HolRm lam) (hA : Antitone lam) :
    ∃ v : Formalism.BasicNotions.nablaSq ℂ n (dw lam), v ≠ 0 ∧
      (∀ a b : Fin n, a < b → Xu lam a b *ᵥ ((wb lam).repr v : Jd n lam → ℂ) = 0) ∧
      ∀ a : Fin n, Xu lam a a *ᵥ ((wb lam).repr v : Jd n lam → ℂ) =
        (lam a : ℂ) • ((wb lam).repr v : Jd n lam → ℂ) := by
  refine ⟨hv lam, hv_ne lam, fun a b hab => ?_, fun a => ?_⟩
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a b (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a b (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun _ => ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a b (1 : ℂ))] with t ht
      rw [Rm_mulVec lam ht, fix_upper lam hab ht]
    have h2 := (hasDerivAt_const (0 : ℂ) (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2
  · ext i
    have h1 := hasDerivAt_mulVec hD (Matrix.single a a (1 : ℂ)) ((wb lam).repr (hv lam)) i
    have hne : ∀ᶠ t : ℂ in 𝓝 0, 1 + t ≠ 0 := by
      have hc : ContinuousAt (fun t : ℂ => 1 + t) 0 := by fun_prop
      exact hc.eventually_ne (by simp)
    have hev : (fun t : ℂ => (Rm lam (1 + t • Matrix.single a a (1 : ℂ)) *ᵥ
        ((wb lam).repr (hv lam) : Jd n lam → ℂ)) i) =ᶠ[𝓝 0]
        fun t => (1 + t) ^ (lam a) * ((wb lam).repr (hv lam) : Jd n lam → ℂ) i := by
      filter_upwards [eventually_line_unit (Matrix.single a a (1 : ℂ)), hne] with t ht ht'
      rw [Rm_mulVec lam ht, diag_act hA a ht' ht]
      simp
    have hz : HasDerivAt (fun t : ℂ => (1 + t) ^ (lam a)) (lam a : ℂ) 0 := by
      have h0 := hasDerivAt_zpow (lam a) ((1 : ℂ) + 0) (Or.inl (by simp))
      have h3 := h0.comp_const_add 1 0
      have e : (lam a : ℂ) * ((1 : ℂ) + 0) ^ (lam a - 1) = lam a := by simp
      rw [e] at h3
      exact h3
    have h2 := (hz.mul_const (((wb lam).repr (hv lam) : Jd n lam → ℂ) i)).congr_of_eventuallyEq hev
    simpa [Xu] using h1.unique h2

end GlobalTheory.CompanionTheory.RmHol.HW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetFormula
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.HeckeAvg

theorem heckeG_eq_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsOpen (J : Set G) → IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (g : G) (U : Module.End ℂ (fixed π J)), PositivityTheory.Lbc.IsHeckeOpG π J g U → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((U v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  intro G _ _ _ J _ hJc V _ _ π hπ g U hU r x hr hxJ hx v
  obtain ⟨E, _hE1, hE2, _hE3, hE4, hE5⟩ := _root_.GlobalTheory.CompanionTheory.CompactAvg.exists_average G J hJc V π hπ
  have hcomp : ∀ (a b : G) (w : V), π a (π b w) = π (a * b) w := by
    intro a b w
    rw [map_mul]
    rfl
  have hv : ∀ k ∈ J, π k (v : V) = v := by
    intro k hk
    have h0 : ∀ hh : J, π hh (v : V) = ((1 : J →* ℂˣ) hh : ℂ) • (v : V) := v.2
    simpa using h0 ⟨k, hk⟩
  have hH : J ⊓ J.map (MulAut.conj g).toMonoidHom ≤ J := inf_le_left
  have hu : ∀ h ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom, π h (π g (v : V)) = π g (v : V) := by
    intro h hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hh).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hcomp, show g * k * g⁻¹ * g = g * k by group, ← hcomp, hv k hk]
  have hEu : E (π g (v : V)) = (r : ℂ)⁻¹ • ∑ i, π (x i) (π g (v : V)) :=
    hE5 (π g (v : V)) _ hH hu r x hr hxJ hx
  have hUv : ((U v : fixed π J) : V) = E (π g (v : V)) := by
    have h1 : E ((U v : fixed π J) : V) = ((U v : fixed π J) : V) := hE2 _ (U v).2
    have key : ∀ l : Module.Dual ℂ V, l (E ((U v : fixed π J) : V) - E (π g (v : V))) = 0 := by
      intro l
      have hf : ∀ y ∈ J, (l ∘ₗ E) ∘ₗ π y = l ∘ₗ E := by
        intro y hy
        rw [LinearMap.comp_assoc, hE4 y hy]
      have h2 := hU v (l ∘ₗ E) hf
      simp only [LinearMap.comp_apply] at h2
      rw [map_sub, h2, sub_self]
    have h3 := (Module.forall_dual_apply_eq_zero_iff ℂ _).mp key
    rw [← h1]
    exact sub_eq_zero.mp h3
  rw [hUv, hEu]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact hcomp _ _ _

end GlobalTheory.CompanionTheory.HeckeAvg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSum
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.HeckeAvg

theorem hecke_eq_average : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (J : Subgroup (GL (Fin N) k)), IsCompact (J : Set (GL (Fin N) k)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (g : GL (Fin N) k) (T : Module.End ℂ (fixed π J)), IsHeckeOp π J g T → ∀ (r : ℕ) (x : Fin r → GL (Fin N) k), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom) → ∀ v : fixed π J, ((T v : fixed π J) : V) = ((r : ℂ)⁻¹) • ∑ i, π (x i * g) (v : V) := by
  intro k _ _ _ _ N J hJ V _ _ π hπ g T hT r x hr hx hy v
  obtain ⟨E, hE1, -, hE3, -, hE5⟩ := _root_.GlobalTheory.CompanionTheory.CompactAvg.exists_average (GL (Fin N) k) J hJ V π hπ
  have hv : ∀ j ∈ J, π j (v : V) = v := fun j hj => by
    have := v.2 ⟨j, hj⟩
    simpa using this
  have hu : ∀ h ∈ J ⊓ J.map (MulAut.conj g).toMonoidHom, π h (π g (v : V)) = π g (v : V) := by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hh.2
    have e : (MulAut.conj g).toMonoidHom j * g = g * j := by simp
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hv j hj]
  have hEu := hE5 (π g (v : V)) (J ⊓ J.map (MulAut.conj g).toMonoidHom) inf_le_left hu r x hr hx hy
  have hsum : ∑ i, π (x i) (π g (v : V)) = ∑ i, π (x i * g) (v : V) :=
    Finset.sum_congr rfl fun i _ => by rw [map_mul, Module.End.mul_apply]
  rw [← hsum, ← hEu]
  have hw : ((T v : fixed π J) : V) - E (π g (v : V)) ∈ fixed π J :=
    Submodule.sub_mem _ (T v).2 (hE1 _)
  have h0 := _root_.GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed (GL (Fin N) k) J hJ V π hπ _ hw (by
    intro l hl
    have h1 : l (E (π g (v : V))) = l (π g (v : V)) := by
      have := hE3 l hl
      exact LinearMap.congr_fun this _
    rw [map_sub, h1, hT v l hl, sub_self])
  exact sub_eq_zero.mp h0

end GlobalTheory.CompanionTheory.HeckeAvg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HighestDeriv

section Coinv

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Coinv

def piFinTwoTensor (X : Fin 2 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] :
    (⨂[ℂ] a, X a) ≃ₗ[ℂ] X 0 ⊗[ℂ] X 1 :=
  ((LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => X i.succ) 0).symm).trans
    (GlobalTheory.SmGL.MultiIrr.tensorCons X)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Two

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t : ℕ}

def piTensorTwoEquiv' (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
  .mk (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)
        (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g)
        (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g) (x false) (x true)).symm

theorem nonempty_prod2_equiv (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod2 (k := k) rfl π₁ π₂).Equiv (prod₂ π₁ π₂)) :=
  ⟨LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv' π₁ π₂)⟩

end Two

section Main

end Main

end GlobalTheory.CompanionTheory.HighestDeriv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDual
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Intertw

variable {n : ℕ}

theorem exp_mem (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem sum_single {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • F x y = c • F a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_neg' (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem family_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ a, ∑ b, X a b • F a b = 0) (a b : Fin n) : F a b = 0 := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg', neg_add,
      add_comm]
  have m1 := h _ h1
  have m2 := h _ h2
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single, one_smul] at m1 m2
  have m3 : F a b + F b a = 0 := by
    have := congrArg (fun v => (-Complex.I) • v) m2
    simpa [smul_add, smul_smul] using this
  have m4 : (2 : ℂ) • F a b = 0 := by
    rw [two_smul]
    calc F a b + F a b = (F a b - F b a) + (F a b + F b a) := by abel
      _ = 0 := by rw [m1, m3, add_zero]
  exact (smul_eq_zero.1 m4).resolve_left two_ne_zero

theorem intertwines : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf →
    ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  intro n V _ _ σ Kf hK E G hG t ht a b ξ
  refine sub_eq_zero.1 (family_eq_zero (fun a b => t (G a b ξ) - Kf a b (t ξ)) (fun X hX => ?_) a b)
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun s => ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem X hX s⟩
  have h1 := hG.2 X γ hX (fun _ => rfl) ξ
  obtain ⟨S, _, hS, _, _, hd⟩ := hK.2 (t ξ)
  have h2 := hd X γ (fun _ => rfl) (t ξ) hS
  let tL : (E.V →L[ℂ] ℂ) →L[ℂ] V := LinearMap.toContinuousLinearMap t
  have h3 : HasDerivAt (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) (tL (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    (tL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
  have h4 : (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) = fun s : ℝ => σ (γ s) (t ξ) := by
    funext s
    exact ht (γ s) ξ
  rw [h4] at h3
  have h5 := h3.unique h2
  have h6 : tL (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • t (G a b ξ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
    rfl
  rw [h6] at h5
  simp only [smul_sub, Finset.sum_sub_distrib, h5, sub_self]

end GlobalTheory.CompanionTheory.RealCountG.Intertw
end
end

