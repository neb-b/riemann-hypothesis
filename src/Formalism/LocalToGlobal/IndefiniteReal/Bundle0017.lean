module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0015

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem definite_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZ (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x
  cases b <;> exact toF_mem_Z _ _ _

theorem definite_coordinates_in_good_part (X : CxData A3.fam3.amb3) (b : Bool) :
    X.CoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem lift_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x
  cases b <;> exact toF_mem_Z _ _ _

theorem lift_coordinates_in_good_part_family (X : CxData A3.fam3.amb3) (b : Bool) :
    X.LiftCoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro j t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem definite_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y
  · rw [hJ t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y

theorem lift_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ j t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y
  · rw [hJ j t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y

theorem definite_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) (hK : X.KFormR)
    (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedR := by
  intro t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl p'))
      fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr k'))
      fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.what₂ t).act g f f'⟩

theorem lift_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) (hK : X.KFormL)
    (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedL := by
  intro j t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH j t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inl p))
      (Sum.inl (Sum.inl p')) fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH j t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inr k))
      (Sum.inl (Sum.inr k')) fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f'⟩

end Concrete3

section Equiv3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

theorem coordinates_mem_subspace {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  exact toF_mem_Z ℓ Z y

theorem part_iff_rows3 (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (p : A3.fam3.base3.Ix)
    (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.R A3.fam3.F.μ0).dZ ℓ (X.Z A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ (X.Z A3.fam3.F.μ0) p.1 ↔
      X.Θ A3.fam3.F.μ0 (X.jR A3.fam3.F.μ0 ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ (X.Z A3.fam3.F.μ0) y)) ∈ X.EEp p := by
  have : FiniteDimensional K (A3.fam3.F.R A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.R A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts p]
  exact mem_eigSum_iff_map ((X.Θ A3.fam3.F.μ0).comp (X.jR A3.fam3.F.μ0)) (hOk.what₂ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.what₂ _) (hOk.what₂ _)) hH.comm
    (fun i v => by
      show X.Θ _ (X.jR _ (A3.fam3.amb3.opR _ (Sum.inl i) v)) = _
      rw [X.jR_opR hR, hH.intw]; rfl)
    (DefFam3.stable3_rows hst A3.fam3.F.μ0) (fun z hz h0 => X.theta_jR_inj hR _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

theorem part_iff_lifts3 (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (j : Fin m)
    (p : A3.fam3.base3.Ix) (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.L j A3.fam3.F.μ0).dZ ℓ (X.Zl j A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.LI j A3.fam3.F.μ0).part3 ℓ (X.Zl j A3.fam3.F.μ0) (A3.fam3.tr3 j p.1) ↔
      X.θ' j A3.fam3.F.μ0 (X.jL j A3.fam3.F.μ0 ((A3.fam3.F.L j A3.fam3.F.μ0).toF ℓ (X.Zl j A3.fam3.F.μ0) y)) ∈ X.Wp j p := by
  have : FiniteDimensional K (A3.fam3.F.L j A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.L j A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts j p]
  exact mem_eigSum_iff_map ((X.θ' j A3.fam3.F.μ0).comp (X.jL j A3.fam3.F.μ0)) (hOk.lifts _ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.lifts _ _) (hOk.lifts _ _))
    (hH.comm j)
    (fun i v => by
      show X.θ' _ _ (X.jL _ _ (A3.fam3.amb3.opL _ _ (Sum.inl i) v)) = _
      rw [X.jL_opL hL, hH.intw]; rfl)
    (DefFam3.stable3_lifts hst j A3.fam3.F.μ0) (fun z hz h0 => X.theta_jL_inj hL j _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
  (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem definite_equivariance_of_primitive (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (b : Bool) :
    X.H3 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro p x
  rw [CxData.iC_cpt_eq]
  cases b
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P0 ψ0) x
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P1 ψ1) x

theorem lift_equivariance_of_primitive (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (b : Bool) :
    X.H3W (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j p x
  rw [CxData.tC_cpt_eq]
  cases b
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P0 ψ0) x
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P1 ψ1) x

end Equiv3

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MajAtEqZeroOfMemQpOfNe
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx.GroupActionMatrices

section Inst3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty : Type}

theorem okOp_opAll {B : BlockDat K G Pl0} {D : InertDat3 B I0 Ty} {s : ℕ} (h : B.Ok s) (hD : D.Ok3) (hH : B.OkH)
    (hH3 : D.InertRationalAdjoint) : OkOp B D.opAll := by
  refine ⟨?_, ?_, hD.comm, InertDat3.splitOver_opAll D h hD, ?_⟩
  · intro i a b
    rcases i with p | k
    · exact hH.rat p a b
    · exact hH3.rat k a b
  · intro i
    rcases i with p | k
    · obtain ⟨p', hp'⟩ := hH.adj p
      exact ⟨Sum.inl p', hp'⟩
    · obtain ⟨k', hk'⟩ := hH3.adj k
      exact ⟨Sum.inr k', hk'⟩
  · intro i g
    rcases i with p | k
    · exact h.opG p g
    · exact hD.opG k g

end Inst3

section Main3

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable (A3 : FamIn3 K G Pl0 I0 Ty T m) (X : CxData A3.fam3.amb3)

theorem proviso_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : ∀ j, (A3.A.fam.L j A3.A.fam.μ0).OkH ∧ (A3.liftI j A3.A.fam.μ0).InertRationalAdjoint)
    (P : Subgroup G) (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
    (hC : LiftsEig3 A3 X P ψ C) : (A3.side3 P ψ X.zs).Proviso := by
  intro j
  have hB := DefFam.blockHyp_lift A3.A.fam hOk.ok2 P ψ j A3.A.fam.μ0
  have hO : OkOp _ (A3.liftI j A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0) (hH j).1 (hH j).2
  have hr := eig_ratG hB hO (C j)
  rw [← hC j] at hr
  exact CyclotomicLifting.xq_rat hB hr

theorem types_of_lift_eigenvalues {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (hst : X.zs.Stable) (P : Subgroup G)
    (ψ : P →* Kˣ) {C : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop} (hC : LiftsEig3 A3 X P ψ C)
    (hT : LiftsTyp3 A3 C) : (A3.side3 P ψ X.zs).Types := by
  intro j
  refine (A3.fam3.LI j A3.A.fam.μ0).inert_parts_span_top (ℓ := A3.A.fam.lvlA P ψ) (Z := X.Zl j A3.A.fam.μ0)
    hOk.ok2.conj (hOk.ok2.lifts j A3.A.fam.μ0) (hOk.lifts j A3.A.fam.μ0)
    hOk.ok2.irr ?_ (fun p : A3.fam3.base3.Ix => A3.fam3.tr3 j p.1) ?_ ?_
  · intro i
    exact Submodule.map_le_iff_le_comap.1 (hst.2 j A3.A.fam.μ0 (Sum.inl i))
  · intro p q hpq
    exact hsep p.1 p.2 q.1 q.2 (fun h => hpq (Subtype.ext h)) j
  · refine (hC j).le.trans ?_
    apply BlockDat.good_part_coordinates_mono
    refine Col.eigSum_mono fun x hx => ?_
    obtain ⟨p, hp, hx'⟩ := hT j x hx
    exact ⟨⟨p, hp⟩, hx'⟩

theorem majAt_eq_zero_of_mem_Qp_of_ne {s : ℕ} (hOk : A3.fam3.Ok3 s) (hH : (A3.A.fam.R A3.A.fam.μ0).OkH ∧ (A3.rowI A3.A.fam.μ0).InertRationalAdjoint)
    (hst : X.zs.Stable) (P : Subgroup G) (ψ : P →* Kˣ) (v : InfinitePlace K) (p q : A3.fam3.base3.Ix) (hpq : p ≠ q)
    (x : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hx : x ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 p)
    (y : Fin ((A3.side3 P ψ X.zs).dQ A3.A.fam.μ0) → K) (hy : y ∈ (A3.side3 P ψ X.zs).Qp A3.A.fam.μ0 q) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((A3.side3 P ψ X.zs).XQ A3.A.fam.μ0) v x y = 0 := by
  have hB : BlockHyp (A3.A.fam.R A3.A.fam.μ0) (A3.A.fam.lvl P ψ) A3.A.fam.v0 s :=
    ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ A3.A.fam.μ0⟩
  have hO : OkOp (A3.A.fam.R A3.A.fam.μ0) (A3.fam3.RI A3.A.fam.μ0).opAll :=
    okOp_opAll (hOk.ok2.what₂ A3.A.fam.μ0) (hOk.what₂ A3.A.fam.μ0) hH.1 hH.2
  refine part_orthg hB hO (fun i => Submodule.map_le_iff_le_comap.1 (hst.1 A3.A.fam.μ0 (Sum.inl i))) v
    (C := (A3.fam3.RI A3.A.fam.μ0).HasRes3 p.1) (C' := (A3.fam3.RI A3.A.fam.μ0).HasRes3 q.1) ?_ hx hy
  intro z hz
  exact (A3.fam3.RI A3.A.fam.μ0).excl3
    ((A3.fam3.RI A3.A.fam.μ0).diffAt_of_mem_ixFin3 q.2 p.2 (fun h => hpq (Subtype.ext h).symm)) z hz

end Main3

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PHeisThA
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem repr_snd (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k = (cE F E z k).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).2
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [sndA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem repr_fst (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) k = (cE F E z k).1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).1
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [fstA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem trace_tmul (e : E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  have h : Algebra.lmul (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) =
      (Algebra.lmul F E e).baseChange (AF F) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange]
  rfl

end Tens

section Sympl

variable {D : D7}

theorem cA_algebraMap (c : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) c) = algebraMap (AF D.host.F) (AE D) c := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (c ⊗ₜ[D.host.F] (1 : D.host.E)) =
    c ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  rw [Algebra.smul_def, map_mul, cA_algebraMap, ← Algebra.smul_def]

end Sympl

end Formalism.IndefR.PHeisTh

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PHeisThC
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC Filter Topology
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

theorem eq_one_of_re_pow_gt (u : ℂ) (hu : ‖u‖ = 1) (h : ∀ n : ℕ, 1 / 2 < (u ^ n).re) : u = 1 := by
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖u - 1‖)
  have h1 : ‖u ^ N - 1‖ ≤ 2 := by
    calc ‖u ^ N - 1‖ ≤ ‖u ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hu]; norm_num
  have h2 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ _i ∈ Finset.range N, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => (h i).le
  have h3 : (N : ℝ) / 2 * ‖u - 1‖ ≤ 2 := by
    calc (N : ℝ) / 2 * ‖u - 1‖ ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right h2 hpos.le
      _ = ‖u ^ N - 1‖ := by rw [← norm_mul, geom_sum_mul]
      _ ≤ 2 := h1
  have h4 : 4 / ‖u - 1‖ * ‖u - 1‖ = 4 := div_mul_cancel₀ _ hpos.ne'
  nlinarith [mul_lt_mul_of_pos_right hN hpos]

theorem psiOpen : PsiOpenP := by
  intro F _ _ ψ hψ
  obtain ⟨hcont, hnorm, -, -⟩ := hψ
  let g : Af F → ℂ := fun y => ψ (pairA F 0 y)
  have hp : Continuous (pairA F 0) := by
    unfold pairA; exact continuous_const.prodMk continuous_id
  have hg : Continuous g := hcont.comp hp
  have gzero : g 0 = 1 := by
    show ψ (pairA F 0 0) = 1
    have e : pairA F 0 0 = 0 := rfl
    rw [e, AddChar.map_zero_eq_one]
  have gadd : ∀ a b, g (a + b) = g a * g b := by
    intro a b
    show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold pairA
    show ((0 : Ainf F), a + b) = ((0 + 0 : Ainf F), a + b)
    rw [add_zero]
  have gnsmul : ∀ (n : ℕ) a, g (n • a) = g a ^ n := by
    intro n a
    induction n with
    | zero => simp [gzero]
    | succ n ih => rw [succ_nsmul, gadd, ih, pow_succ]
  let G : AddSubgroup (Af F) :=
    { carrier := {y | ∀ z ∈ Ohat F, g (z * y) = 1}
      zero_mem' := by
        intro z _
        rw [mul_zero]; exact gzero
      add_mem' := by
        intro a b ha hb z hz
        rw [mul_add, gadd, ha z hz, hb z hz, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := gadd (z * -a) (z * a)
        rw [← mul_add, neg_add_cancel, mul_zero, gzero, ha z hz, mul_one] at h1
        exact h1.symm }
  refine ⟨G, ?_, ?_, ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds G (g := 0) ?_
    have key : ∀ᶠ d in 𝓝 (0 : Af F), ∀ z ∈ Ohat F, 1 / 2 < (g (z * d)).re := by
      refine (isCompact_Ohat F).eventually_forall_of_forall_eventually fun z _ => ?_
      have hc : Continuous fun p : Af F × Af F => (g (p.2 * p.1)).re :=
        Complex.continuous_re.comp (hg.comp (continuous_snd.mul continuous_fst))
      have h0 : 1 / 2 < (g (z * 0)).re := by rw [mul_zero, gzero]; norm_num
      exact (isOpen_lt continuous_const hc).mem_nhds h0
    refine Filter.mem_of_superset key fun d hd z hz => ?_
    apply eq_one_of_re_pow_gt _ (hnorm _)
    intro n
    have hnz : n • z ∈ Ohat F :=
      SetLike.mem_coe.mpr (nsmul_mem (SetLike.mem_coe.mp hz) n)
    have := hd _ hnz
    rwa [smul_mul_assoc, gnsmul] at this
  · intro y hy z hz w hw
    show g (w * (z * y)) = 1
    rw [← mul_assoc]
    exact hy _ (SetLike.mem_coe.mpr (mul_mem (SetLike.mem_coe.mp hw) (SetLike.mem_coe.mp hz)))
  · intro y hy
    have := hy 1 (SetLike.mem_coe.mpr (one_mem _))
    rwa [one_mul] at this

theorem psiSmooth : PsiSmoothP := by
  intro D ψ hψ k s hs
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := hψ
  have h := hall θ hθ
  have hc : ∀ ρ, ContDiff ℝ ∞ fun t : Fin k → ℝ => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro ρ
    let L : (Fin k → ℝ) →+ ℂ :=
      { toFun := fun t => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))
        map_zero' := by simp
        map_add' := fun a b => by simp [map_add (f := _), TensorProduct.add_tmul] }
    have hL : Continuous L := (hθ ρ).2.comp hs
    exact (L.toRealLinearMap hL).contDiff
  have e : (fun t => ψ (pairA D.host.F (s t) 0)) = fun t =>
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) *
        ∑ ρ, θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    funext t; exact h (s t)
  rw [e]
  exact (contDiff_const.mul (ContDiff.sum fun ρ _ => hc ρ)).cexp

end Formalism.IndefR.PHeisTh

end
end

