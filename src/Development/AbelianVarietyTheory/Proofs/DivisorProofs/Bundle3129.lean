module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixglobA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemOfStanding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegWLocalFunctionsThetaPureTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleMatch
section
noncomputable section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TopFlip

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.TripleAssembly GlobalTheory.RouteSeesaw GlobalTheory.SquareIdent
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM)

theorem pureT_smul {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] {s ξ ξ' : ∀ i, N i}
    (h : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ) (h' : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ') {c : ι → ℂ} (hc : (Function.mulSupport c).Finite)
    (e : ∀ i, ξ' i = c i • ξ i) : GlobalTheory.SmallThetaModules.pureT s ξ' = (∏ᶠ i, c i) • GlobalTheory.SmallThetaModules.pureT s ξ := by
  apply Subtype.ext
  rw [Submodule.coe_smul, GlobalTheory.SmallThetaModules.coe_pureT h, GlobalTheory.SmallThetaModules.coe_pureT h']
  funext l
  simp only [GlobalTheory.SmallThetaModules.evFam, Pi.smul_apply, smul_eq_mul, e, map_smul]
  exact finprod_mul_distrib hc (GlobalTheory.SmallThetaModules.mulSupport_fin h l)

variable {D : D7}


end GlobalTheory.TopFlip

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem pureT_loc (hL : L.Is μ₀) {t : T} {i j : ℕ} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} {om om' R Rf} (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf) (hti : IsTied t i j e Bs Γ X)
    {φ φ'} (h : IsFinPart Γ.M X.T φ) (h' : IsFinPart Γ.M' X.T φ') {c : Pl D.host.E → ℂ}
    (hc : ∀ w ∈ locPl G t, Rf.p _ (φ (w.under (𝓞 D.host.F))) = c w • Rf.p' _ (φ' (w.under (𝓞 D.host.F)))) :
    (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p v (φ v)) =
      (∏ w ∈ locPl G t, c w) • GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (φ' v) := by
  classical
  let c' : Pl D.host.F → ℂ := fun v => ∏ w ∈ locPl G t with w.under (𝓞 D.host.F) = v, c w
  have h1 : ∀ v, v ∉ X.T → c' v = 1 := fun v hv => Finset.prod_eq_one fun w hw => by
    obtain ⟨a, b⟩ := Finset.mem_filter.1 hw
    exact absurd ((hti.2.2.1 v).2 ⟨w, a, b⟩) hv
  have hs : Function.mulSupport c' ⊆ X.T := fun v hv => by_contra fun h => hv (h1 v h)
  rw [pureT_smul (s := GlobalTheory.TripleAssembly.vacIm Γ Rf) (ξ := fun v => Rf.p' v (φ' v)) (ξ' := fun v => Rf.p v (φ v)) (c := c') (X.T.finite_toSet.subset fun v hv => by_contra fun hn => hv (by
      exact (congrArg (Rf.p' v) (h'.2 v hn)).trans (hm.fin.sph v hn).1.symm))
    (X.T.finite_toSet.subset fun v hv => by_contra fun hn => hv (congrArg (Rf.p v) (h.2 v hn))) (X.T.finite_toSet.subset hs) fun v => ?_,
    finprod_eq_prod_of_mulSupport_subset _ hs,
    Finset.prod_fiberwise_of_maps_to fun w hw => (hti.2.2.1 _).2 ⟨w, hw, rfl⟩]
  by_cases hv : v ∈ X.T
  · obtain ⟨w, hw, rfl⟩ := (hti.2.2.1 v).1 hv
    have : c' (w.under (𝓞 D.host.F)) = c w := Finset.prod_eq_single_of_mem w (Finset.mem_filter.2 ⟨hw, rfl⟩)
      fun w' hw' hne => absurd (Good.under_injOn hL G t (Finset.mem_filter.1 hw').1 hw (Finset.mem_filter.1 hw').2) hne
    rw [this, hc w hw]
  · rw [h1 v hv, one_smul, h.2 v hv, h'.2 v hv, (hm.fin.sph v hv).1]

end GlobalTheory.TopFlip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationThetaEquivariance
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinExist

section Dual

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {Q : LB (A ⊗ B).left}

theorem evc_mul_right (hQ' : IsDual B A (swap Q)) (hQ : Q.IsLB) {Y : Over S} (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
  have e := (isAdditive_iff hQ'.isLB).1 hQ'.additive Y b b' a
  rwa [evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB] at e

theorem eq_of_evc (hQ : IsDual A B Q) {T : Over S} (x y : T ⟶ B)
    (h : evc hQ.isLB (fst A T) (snd A T ≫ x) = evc hQ.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev Q (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hQ.isLB _
  have hadd : IsAdditive (ev Q (fst A T) (snd A T ≫ x)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t => ?_
    rw [evc_ev hQ.isLB, evc_ev hQ.isLB, evc_ev hQ.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hQ.isLB).1 hQ.additive Y a a' (t ≫ x)
  refine (hQ.univ T _ hM hadd).unique ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hQ.isLB _)).1 ?_)
  rw [cls_ev hQ.isLB, cls_ev hQ.isLB]
  exact h

end Dual

section Siegel

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)

theorem evc_mul_left (hA : Out.RelAmple c.A c.diag) {Y : Over S} (a a' b : Y ⟶ c.A) :
    evc c.isLB (a * a') b = evc c.isLB a b + evc c.isLB a' b :=
  GlobalTheory.PrincipalIntegral.pair_mul c GlobalTheory.SemiRigid.globalFns hA Y a a' b

theorem evc_comm {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc c.isLB b a :=
  GlobalTheory.PrincipalIntegral.pair_comm c Y a b

theorem isAdditive_P (hA : Out.RelAmple c.A c.diag) : IsAdditive c.P :=
  (isAdditive_iff c.isLB).2 fun _ a a' b => evc_mul_left c hA a a' b

variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem evc_la (hQ : Q.IsLB) {la : c.A ⟶ B} (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la)))
    {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc hQ a (b ≫ la) := by
  have e := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff c.isLB (pull_isLB hQ _)).2 hla)
  rw [cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc] at e
  exact e

end Siegel

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

section Main

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem isMonHom_la (hA : Out.RelAmple c.A c.diag) (hQ : IsDual c.A B Q) (hQ' : IsDual B c.A (swap Q)) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) : IsMonHom la := by
  refine isMonHom_of_mul la fun T x y => eq_of_evc hQ _ _ ?_
  rw [← Category.assoc, ← evc_la c hQ.isLB hla, comp_mul, comp_mul, evc_mul_right hQ' hQ.isLB, ← Category.assoc,
    ← Category.assoc, ← evc_la c hQ.isLB hla, ← evc_la c hQ.isLB hla,
    evc_comm c (fst c.A T) ((snd c.A T ≫ x) * (snd c.A T ≫ y)), evc_mul_left c hA, evc_comm c _ (fst c.A T),
    evc_comm c _ (fst c.A T)]

theorem pow_eq_one_of_la {d : ℕ} (hK : SiegKerBy c d) (hQ : IsDual c.A B Q) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) {T : Over S} (x : T ⟶ c.A) (hx : x ≫ la = 1) :
    x ^ d = 1 := by
  refine hK.2 T x ((cls_eq_zero_iff (pull_isLB c.isLB _)).1 ?_)
  change evc c.isLB (snd c.A T ≫ x) (fst c.A T) = 0
  rw [evc_comm c, evc_la c hQ.isLB hla, Category.assoc, hx, MonObj.comp_one, evc_one_right hQ.isLB hQ.zero]

end Main

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

open GlobalTheory.ZarhinFam

theorem exists_zData : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (B : Over S) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A), GlobalTheory.ZarhinFam.ZData c d B Q la mu := by
  intro h M d S t c _ _ _ hd _ _ hK
  obtain ⟨B, iB, Q, hB, -, hQ, hQ'⟩ := GlobalTheory.dualAbelianScheme S c.A c.ab
  obtain ⟨la, hla, -⟩ := hQ.univ c.A c.P c.isLB (isAdditive_P c hK.1)
  have hmon := isMonHom_la c hK.1 hQ hQ' hla
  obtain ⟨mu, hmu, h1, h2⟩ := GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker S c.A B Q la d c.ab hB hQ hQ' hmon hd
    fun T x hx => pow_eq_one_of_la c hK hQ hla x hx
  exact ⟨B, iB, hB.comm, Q, la, mu, hB, hQ, hQ', hmon, hmu, h1, h2, hla⟩

end GlobalTheory.ZarhinExist
end
end

