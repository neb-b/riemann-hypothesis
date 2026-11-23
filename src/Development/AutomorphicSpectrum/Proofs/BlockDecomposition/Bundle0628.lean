module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import GroundTheory.AutomorphicForms.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExist
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0621

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegNcjm

theorem exists_perm_of_map_eq {α : Type*} {l : ℕ} {x y : Fin l → α}
    (h : Finset.univ.val.map y = Finset.univ.val.map x) : ∃ e : Equiv.Perm (Fin l), ∀ a, y a = x (e a) :=
  _root_.UpperTheory.Reformulated.B.Yhb6.main h

theorem exists_perm_one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l N : ℕ} (x : Fin l → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = N) (hxc : ∀ a, (x a).IsCusp) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (h : IsSubquotient π (prodIrr x hx)),
    ∃ (e : Equiv.Perm (Fin l)) (he : ∑ a, (x (e a)).1 = N), 1 ≤ jm (fun a => x (e a)) he π := by
  intro k _ _ _ _ hA l N x hx hxc V _ _ π hs hi h
  obtain ⟨c, y, hy, hyc, φ, hφ⟩ := _root_.GlobalTheory.CompanionTheory.SubEmb.subEmbedding k N V π hs hi
  have h1 : HasSupport π (Finset.univ.val.map x) := hasSupport_of_isSubquotient hi hxc h
  have h2 : HasSupport π (Finset.univ.val.map y) := hasSupport_of_isSubquotient hi hyc (.of_injective φ hφ)
  have hm := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness h2 h1
  have hcl : c = l := by simpa using congrArg Multiset.card hm
  subst hcl
  obtain ⟨e, he⟩ := exists_perm_of_map_eq hm
  obtain rfl : y = fun a => x (e a) := funext he
  refine ⟨e, hy, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA _ hy π hs φ ?_⟩
  have : Nontrivial V := GlobalTheory.SmGL.nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun h0 => hv (hφ (h0.trans (map_zero φ).symm))⟩

end GlobalTheory.CompanionTheory.SegNcjm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegFineCons

theorem finSigmaFinEquiv_one_val {s : ℕ} (i : Fin s) (b : Fin 1) :
    ((finSigmaFinEquiv (m := s) (n := fun _ => 1) ⟨i, b⟩ : Fin _) : ℕ) = i := by
  rw [finSigmaFinEquiv_apply, Subsingleton.elim b 0]
  simp

theorem eq_one_of_sum_eq {s : ℕ} (c : Fin s → ℕ) (h1 : ∀ a, 1 ≤ c a) (h : ∑ a, c a = s) (a : Fin s) : c a = 1 := by
  have h2 : ∑ _a : Fin s, 1 = ∑ a, c a := by simpa using h.symm
  exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => h1 i)).1 h2 a (Finset.mem_univ a)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem sum_concat_fst {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) :
    ∑ i, (concat c x i).1 = ∑ a, ∑ b, (x a b).1 := by
  rw [← Fintype.sum_sigma' (fun a b => (x a b).1)]
  exact Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)


omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem concat_finSigmaFinEquiv {s : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL (k := k)) (p : Σ a, Fin (c a)) :
    concat c x (finSigmaFinEquiv p) = x p.1 p.2 := by
  have key : ∀ q : Σ a, Fin (c a), q = p → x q.1 q.2 = x p.1 p.2 := by
    rintro _ rfl
    rfl
  exact key _ (Equiv.symm_apply_apply _ _)

theorem exists_cusp_word (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL (k := k)) :
    ∃ (c : ℕ) (x : Fin c → IrrGL (k := k)) (hd : ∑ b, (x b).1 = y.1), (∀ b, (x b).IsCusp) ∧ 1 ≤ jm x hd y.rep := by
  obtain ⟨c, x, hd, hc, φ, hφ⟩ := GlobalTheory.CompanionTheory.SubEmb.subEmbedding k y.1 _ y.rep y.2.rep.smooth y.2.rep.irr
  have := Model.nontrivial_of_isIrreducible y.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.2.rep.V)
  exact ⟨c, x, hd, hc, GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA x hd _ y.2.rep.smooth φ
    ⟨v, fun h => hv (hφ (h.trans (map_zero φ).symm))⟩⟩

theorem equiv_piTensor_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Γ : Segment k) (hF : FineJac Γ) (u : IrrGL (k := k)) (hu : IsLSeg Γ u.rep) (hs : ∑ i, (dec Γ i).1 = u.1) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Levi k fun i => Fin ((dec Γ i).1)) X), ρ.IsIrreducible → IsSubquotient ρ (jac (stdBlocks (fun i => (dec Γ i).1) hs) u.rep) → Nonempty (ρ.Equiv (piTensor fun i => (dec Γ i).rep)) := by
  intro k _ _ _ _ hA Γ hF u hu hs X _ _ ρ hi hsub
  have hsm : IsSmooth ρ := hsub.isSmooth (isSmooth_jac _ u.2.rep.smooth)
  obtain ⟨σ, ⟨E⟩⟩ := _root_.GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA (fun i => (dec Γ i).1) (⟨X, ρ, hsm, hi⟩ : IrrRep _)
  replace E : ρ.Equiv (piTensor fun a => (σ a).rep.ρ) := E
  suffices hσ : σ = fun a => (dec Γ a).2 by
    subst hσ
    exact ⟨E⟩
  let y : Fin Γ.len → IrrGL (k := k) := fun i => ⟨(dec Γ i).1, σ i⟩
  have hy : ∑ a, (y a).1 = u.1 := hs
  have h1 : 1 ≤ jm y hy u.rep := Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2
    ((IsSubquotient.of_surjective E.toIntertwiningMap E.toLinearEquiv.surjective).trans hsub))
  choose c x hd hcusp hpos using fun a => exists_cusp_word hA (y a)
  have hcat : ∑ i, (concat c x i).1 = u.1 := by
    rw [sum_concat_fst, ← hy]
    exact Finset.sum_congr rfl fun a _ => hd a
  have h2 : 1 ≤ jm (concat c x) hcat u.rep := h1.trans
    (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy c x hd hcat hpos u.rep u.2.rep.smooth
      (hasFiniteLength_of_isIrreducible u.2.rep.irr))
  obtain ⟨h, hcon⟩ := (hF u.rep hu).2 _ (concat c x) hcat (fun a => hcusp _ _) h2
  have hc0 : ∀ a, 1 ≤ c a := fun a => by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => ?_
    have : IsEmpty (Fin (c a)) := by rw [h0]; exact Fin.isEmpty
    have h3 : (y a).1 = 0 := by rw [← hd a]; simp
    exact Γ.d_pos.ne' h3
  obtain rfl : c = fun _ => 1 := funext (eq_one_of_sum_eq c hc0 h)
  funext a
  have h3 : x a 0 = dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) :=
    (concat_finSigmaFinEquiv _ x ⟨a, 0⟩).symm.trans (hcon (finSigmaFinEquiv ⟨a, 0⟩))
  have h4 : dec Γ (Fin.cast h (finSigmaFinEquiv ⟨a, 0⟩)) = dec Γ a :=
    congrArg _ (Fin.ext (finSigmaFinEquiv_one_val a 0))
  have h5 : x a 0 = y a := GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm (y a) (y a).rep (.refl _) (x a) (hd a) (hpos a)
  have h6 : (⟨(dec Γ a).1, σ a⟩ : IrrGL (k := k)) = ⟨(dec Γ a).1, (dec Γ a).2⟩ := (h5.symm.trans h3).trans h4
  exact sigma_mk_injective (β := fun n => IrrCl (GL (Fin n) k)) h6

end GlobalTheory.CompanionTheory.SegFineCons

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_principalSeriesSpace_of_indSp {n : ℕ} (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n))
      ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)) :
    (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) :=
  _root_.GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace k n α f

theorem isSatakeParameter_of_isSubquotient_of_injective {n : ℕ} (α : Fin n → ℂˣ) {X V : Type}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) k) X}
    (hρ : IsSmooth ρ) (ι : ρ.IntertwiningMap (principalSeries k n (paramChar k α))) (hι : Function.Injective ι)
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π ρ)
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  _root_.GlobalTheory.CompanionTheory.HeckeSub.isSatakeParameter_subquotient k n α X V ρ hρ ι hι π h μ

theorem KO_eq_integralGL (n : ℕ) : KO k (Fin n) = GroundTheory.Automorphic.GLnLocal.integralGL k n := rfl

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) : fixed ρ H = GroundTheory.Automorphic.fixedVectors ρ H := by
  ext v
  simp [fixed, eig, GroundTheory.Automorphic.fixedVectors]

def bridge {n : ℕ} (α : Fin n → ℂˣ) :
    (prinSeries fun i => unrChar k (α i)).IntertwiningMap (principalSeries k n (paramChar k α)) where
  toFun f := ⟨fun g => f.1.1 g, mem_principalSeriesSpace_of_indSp α f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' g := LinearMap.ext fun f => Subtype.ext (funext fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl)

theorem bridge_injective {n : ℕ} (α : Fin n → ℂˣ) : Function.Injective (bridge (k := k) α) := fun f f' e =>
  by
  have := congrArg Subtype.val e
  apply Subtype.ext
  apply Subtype.ext
  exact this

theorem isSatakeParameter_of_isSubquotient {n : ℕ} (α : Fin n → ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (h : IsSubquotient π (prinSeries fun i => unrChar k (α i)))
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μ : MeasureTheory.Measure (GL (Fin n) k))
    [μ.IsHaarMeasure] : IsSatakeParameter π μ α :=
  isSatakeParameter_of_isSubquotient_of_injective α (isSmooth_parInd _ _) (bridge α) (bridge_injective α) h μ

theorem hasSupport_prinSeries (n : ℕ) (χ : Fin n → kˣ →* ℂˣ) (hχ : ∀ i, IsSmoothChar (χ i))
    (π : IrrRep (GL (Fin n) k)) (h : IsSubquotient π.ρ (prinSeries χ)) :
    HasSupport π.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (χ i) (hχ i)) := by
  have H : GlobalTheory.SmGL.IsCuspSupport π.ρ (fun _ : Fin n => 1) fun a => detRep (Fin 1) (χ a) :=
    ⟨π.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hχ a)⟩, _,
      h.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ)⟩
  exact hasSupport_of_isCuspSupport H

end GlobalTheory.CompanionTheory.SphSupp

namespace GlobalTheory.CompanionTheory.SphSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSpherical_iff_fixedVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) :
    IsSpherical π ↔ GroundTheory.Automorphic.fixedVectors π (GroundTheory.Automorphic.GLnLocal.integralGL k n) ≠ ⊥ := by
  show fixed π (KO k (Fin n)) ≠ ⊥ ↔ _
  rw [KO_eq_integralGL, fixed_eq_fixedVectors]

end GlobalTheory.CompanionTheory.SphSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndexEqDiagonal
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.Tr

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem isInt_mul {r s t : Type} [Fintype s] {M : Matrix r s (w.adicCompletion E)}
    {N : Matrix s t (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact (Ov E w).sum_mem fun k _ => (Ov E w).mul_mem (hM i k) (hN k j)

theorem isInt_of_GLint {n : ℕ} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLint (Fin n) (Ov E w)) :
    IsInt w g.val := by
  obtain ⟨f, rfl⟩ := hg
  intro i j
  exact (f.val i j).2

theorem isInt_sandwich {r s : ℕ} {u : GL (Fin r) (w.adicCompletion E)} {v : GL (Fin s) (w.adicCompletion E)}
    (hu : u ∈ GLint (Fin r) (Ov E w)) (hv : v ∈ GLint (Fin s) (Ov E w))
    (M : Matrix (Fin r) (Fin s) (w.adicCompletion E)) : IsInt w (u.val * M * v.val) ↔ IsInt w M := by
  constructor
  · intro h
    have key := isInt_mul (isInt_mul (isInt_of_GLint (inv_mem hu)) h) (isInt_of_GLint (inv_mem hv))
    have h1 : (u⁻¹).val * u.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : v.val * (v⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : (u⁻¹).val * (u.val * M * v.val) * (v⁻¹).val = M := by
      calc (u⁻¹).val * (u.val * M * v.val) * (v⁻¹).val
          = ((u⁻¹).val * u.val) * M * (v.val * (v⁻¹).val) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at key
  · intro h
    exact isInt_mul (isInt_mul (isInt_of_GLint hu) h) (isInt_of_GLint hv)

def phi {a b : ℕ} {L : Type} [Field L] (p : GL (Fin a) L) (q : GL (Fin b) L) :
    Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := p.val * X * (q⁻¹).val
  invFun Y := (p⁻¹).val * Y * q.val
  left_inv X := by
    have h1 : (p⁻¹).val * p.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (q⁻¹).val * q.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (p⁻¹).val * (p.val * X * (q⁻¹).val) * q.val
        = ((p⁻¹).val * p.val) * X * ((q⁻¹).val * q.val) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  right_inv Y := by
    have h1 : p.val * (p⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : q.val * (q⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc p.val * ((p⁻¹).val * Y * q.val) * (q⁻¹).val
        = (p.val * (p⁻¹).val) * Y * (q.val * (q⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]

theorem relIndex_of_equiv {A B : Type} [AddGroup A] [AddGroup B] (φ : A ≃+ B) (H K : AddSubgroup A)
    (H' K' : AddSubgroup B) (hH : ∀ X, X ∈ H ↔ φ X ∈ H') (hK : ∀ X, X ∈ K ↔ φ X ∈ K') :
    H.relIndex K = H'.relIndex K' := by
  have key : ∀ (P : AddSubgroup A) (P' : AddSubgroup B), (∀ X, X ∈ P ↔ φ X ∈ P') →
      P.map φ.toAddMonoidHom = P' := by
    intro P P' h
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (h X).1 hX
    · intro hY
      exact ⟨φ.symm Y, (h _).2 (by simpa using hY), by simp⟩
  rw [← key H H' hH, ← key K K' hK]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective).symm

theorem mem_latD {ϖ : w.adicCompletion E} {a b i j : ℕ} {W : Matrix (Fin a) (Fin b) (w.adicCompletion E)} :
    W ∈ latD ϖ a b i j ↔
      ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w := Iff.rfl

theorem unif_mem {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ∈ Ov E w := by
  have : Valued.v ϖ ≤ 1 := by
    rw [h]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this

theorem unif_ne {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  intro h0
  rw [IsUnifV, h0, map_zero] at h
  exact WithZero.zero_ne_coe h

theorem diag_iff_latD {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {a b : ℕ} (i j : ℕ)
    (W : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (IsInt w (diagJ a ϖ i * W) ∧ IsInt w (ϖ • (W * diagJ b ϖ⁻¹ j))) ↔ W ∈ latD ϖ a b i j := by
  have hm := unif_mem hϖ
  have h0 := unif_ne hϖ
  have hc : ∀ x : w.adicCompletion E, ϖ * (x * ϖ⁻¹) = x := fun x => by field_simp
  rw [mem_latD]
  constructor
  · rintro ⟨h1, h2⟩ r s
    have a1 := h1 r s
    have a2 := h2 r s
    simp only [diagJ, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at a1 a2
    by_cases hr : (r : ℕ) < i <;> by_cases hs : (s : ℕ) < j
    · rw [if_neg (by omega)]
      rw [if_pos hs, hc] at a2
      exact a2
    · rw [if_pos ⟨hr, by omega⟩]
      rw [if_pos hr] at a1
      exact a1
    · rw [if_neg (by omega)]
      rw [if_neg hr, one_mul] at a1
      exact a1
    · rw [if_neg (by omega)]
      rw [if_neg hr, one_mul] at a1
      exact a1
  · intro h
    refine ⟨fun r s => ?_, fun r s => ?_⟩
    · have a := h r s
      simp only [diagJ, Matrix.diagonal_mul]
      by_cases hr : (r : ℕ) < i
      · rw [if_pos hr]
        by_cases hs : j ≤ (s : ℕ)
        · rwa [if_pos ⟨hr, hs⟩] at a
        · rw [if_neg (by omega)] at a
          exact (Ov E w).mul_mem hm a
      · rw [if_neg hr, one_mul]
        rwa [if_neg (by omega)] at a
    · have a := h r s
      simp only [diagJ, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
      by_cases hs : (s : ℕ) < j
      · rw [if_pos hs, hc]
        rwa [if_neg (by omega)] at a
      · rw [if_neg hs, mul_one]
        by_cases hr : (r : ℕ) < i
        · rwa [if_pos ⟨hr, by omega⟩] at a
        · rw [if_neg (by omega)] at a
          exact (Ov E w).mul_mem hm a

theorem diagJ_mul_inv {L : Type} [Field L] {ϖ : L} (h0 : ϖ ≠ 0) (n j : ℕ) :
    diagJ n ϖ j * diagJ n ϖ⁻¹ j = 1 := by
  rw [diagJ, diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext r
  split_ifs <;> simp [h0]

theorem mem_latM_iff {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {a b i j : ℕ}
    {m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)}
    {k₁ p : GL (Fin a) (w.adicCompletion E)} {k₂ q : GL (Fin b) (w.adicCompletion E)}
    (hk₁ : k₁ ∈ GLint (Fin a) (Ov E w)) (hp : p ∈ GLint (Fin a) (Ov E w))
    (hk₂ : k₂ ∈ GLint (Fin b) (Ov E w)) (hq : q ∈ GLint (Fin b) (Ov E w))
    (e₁ : m.1.val = k₁.val * diagJ a ϖ i * p.val) (e₂ : m.2.val = k₂.val * diagJ b ϖ j * q.val)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    X ∈ latM ϖ m ↔ phi p q X ∈ latD ϖ a b i j := by
  set W := phi p q X with hW
  have hX : X = (p⁻¹).val * W * q.val := ((phi p q).symm_apply_apply X).symm
  have hpp : p.val * (p⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqq : q.val * (q⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hkk : k₂.val * (k₂⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD := diagJ_mul_inv (unif_ne hϖ) b j
  have f₁ : m.1.val * X = k₁.val * (diagJ a ϖ i * W) * q.val := by
    calc m.1.val * X = k₁.val * diagJ a ϖ i * (p.val * (p⁻¹).val) * W * q.val := by
          rw [e₁, hX]; simp only [Matrix.mul_assoc]
      _ = k₁.val * (diagJ a ϖ i * W) * q.val := by
          rw [hpp, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hx : m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val) = 1 := by
    calc m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val)
        = k₂.val * diagJ b ϖ j * (q.val * (q⁻¹).val) * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
          rw [e₂]; simp only [Matrix.mul_assoc]
      _ = k₂.val * (diagJ b ϖ j * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
          rw [hqq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD, Matrix.mul_one, hkk]
  have hinv : (m.2⁻¹).val = (q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
    calc (m.2⁻¹).val = (m.2⁻¹).val * (m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val)) := by
          rw [hx, Matrix.mul_one]
      _ = ((m.2⁻¹).val * m.2.val) * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val) := by
          simp only [Matrix.mul_assoc]
      _ = (q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have f₂ : ϖ • (X * (m.2⁻¹).val) = (p⁻¹).val * (ϖ • (W * diagJ b ϖ⁻¹ j)) * (k₂⁻¹).val := by
    have : X * (m.2⁻¹).val = (p⁻¹).val * (W * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
      calc X * (m.2⁻¹).val
          = (p⁻¹).val * W * (q.val * (q⁻¹).val) * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
            rw [hinv, hX]; simp only [Matrix.mul_assoc]
        _ = (p⁻¹).val * (W * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
            rw [hqq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
  have s₁ := isInt_sandwich hk₁ hq (diagJ a ϖ i * W)
  have s₂ := isInt_sandwich (inv_mem hp) (inv_mem hk₂) (ϖ • (W * diagJ b ϖ⁻¹ j))
  rw [← diag_iff_latD hϖ i j W, ← s₁, ← s₂, ← f₁, ← f₂]
  exact Iff.rfl

theorem latM_relIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (i j : ℕ), i ≤ a → j ≤ b → ∀ m : GLw a w × GLw b w, Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 → Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 → (intSub a b w).relIndex (latM ϖ m) = (intSub a b w).relIndex (latD ϖ a b i j) := by
  intro E _ _ _ a b w ϖ hϖ i j _ _ m h₁ h₂
  obtain ⟨k₁, hk₁, p, hp, e₁⟩ := Set.mem_of_indicator_ne_zero h₁
  obtain ⟨k₂, hk₂, q, hq, e₂⟩ := Set.mem_of_indicator_ne_zero h₂
  refine relIndex_of_equiv (phi p q) _ _ _ _ (fun X => ?_) (mem_latM_iff hϖ hk₁ hp hk₂ hq e₁ e₂)
  constructor
  · intro h
    exact (isInt_sandwich hp (inv_mem hq) X).2 h
  · intro h
    exact (isInt_sandwich hp (inv_mem hq) X).1 h

end GlobalTheory.CompanionTheory.CtS.Tr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExistStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_matrix_permutation_equivs_exist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (e : Fin c ≃ Fin l), (∀ a, y a = x (e a)) → ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)), (∀ i j, b.1 i j = if e j = i then (x i).1 else 0) → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | exact GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij | (intros; apply GlobalTheory.CompanionTheory.CellBij.jhMult_cell_bij <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothParabolicInductionProductStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_parabolic_induction_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), IsSmooth π₁ → IsSmooth π₂ → IsSmooth (sQ h π₁ π₂) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | exact GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | (intros; apply GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveIntertwinerQuotientEquivStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_intertwiner_quotient_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (R : ρ.IntertwiningMap τ), Function.Surjective R → ∃ S : Subrepresentation ρ, S.toSubmodule = LinearMap.ker R.toLinearMap ∧ Nonempty ((subQuot ⊤ S).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | exact GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv | (intros; apply GlobalTheory.CompanionTheory.BZRes.KerQuot.exists_subQuot_top_ker_equiv <;> assumption)
end

