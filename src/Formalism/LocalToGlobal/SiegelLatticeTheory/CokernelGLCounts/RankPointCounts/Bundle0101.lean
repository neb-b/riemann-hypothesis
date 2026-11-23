module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0099
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGood
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem ring_inverse_eq {K : Type*} [CommRing K] {x y : K} (h : x * y = 1) : Ring.inverse x = y := by
  have hx : IsUnit x := ⟨⟨x, y, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = y := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hx, one_mul]

theorem cj_mem_O {p : PlF D} {x : (D.s.atP p).Ep} (hx : x ∈ (D.s.atP p).O) : (D.s.atP p).cj x ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hx ⊢
  exact hx.map (((D.s.atP p).cj.toAlgHom).restrictScalars 𝒪[(D.s.atP p).Fp])

theorem lOf_ρOf_int {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none)
    (hδ : δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (huP : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (a b : Formalism.L2.SG.PairVal.MatR D) (ha : ∀ i j, (D.s.atP p).ιE (a i j) ∈ (D.s.atP p).O)
    (hb : ∀ i j, (D.s.atP p).ιE (b i j) ∈ (D.s.atP p).O) :
    (∀ i j, lOf δ M p a b i j ∈ (D.s.atP p).O) ∧ ∀ i j, ρOf δ M p a b i j ∈ (D.s.atP p).O := by
  obtain ⟨-, hδ0, hcj, -, -, -⟩ := hA
  set Op := (D.s.atP p).O
  set c : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
  set ci : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)
  have hcO : c ∈ Op := Op.mul_mem (alg_mem_O hδ.1) huP.1
  have hciO : ci ∈ Op := Op.mul_mem (alg_mem_O hδ.2) huP.2
  have hcc : c * ci = 1 := by
    have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have h2 : (D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (unitAt_ne p), map_one]
    calc c * ci = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) *
          ((D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
  have hfr : ∀ i, frFac δ p i = ci ^ (D.R.rS - i.val) := fun i => by
    unfold frFac
    exact ring_inverse_eq (by rw [← mul_pow, hcc, one_pow])
  have hfri : ∀ i, Ring.inverse (frFac δ p i) = c ^ (D.R.rS - i.val) := fun i => by
    rw [hfr]; exact ring_inverse_eq (by rw [← mul_pow, mul_comm, hcc, one_pow])
  have hcjfr : ∀ i, ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i) =
      (D.s.atP p).cj ci ^ (D.R.rS - i.val) := fun i => by
    rw [hfr, hcj]; simp
  have hcjfri : ∀ i, Ring.inverse (((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i)) =
      (D.s.atP p).cj c ^ (D.R.rS - i.val) := fun i => by
    rw [hcjfr]
    refine ring_inverse_eq ?_
    rw [← mul_pow, ← map_mul, mul_comm, hcc, map_one, one_pow]
  have hs1 : ∀ x : D.host.E, (D.s.atP p).ιE x ∈ Op → (D.s.atP p).ιE ((-1) ^ (D.R.rS - 0) * x) ∈ Op := fun x hx => by
    rw [map_mul]; exact Op.mul_mem (by rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _) hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [lOf, hs, lL, Matrix.of_apply]
    rw [hcjfr, hcjfri]
    exact Op.mul_mem (Op.mul_mem (Op.pow_mem (cj_mem_O hciO) _) (ha i j)) (Op.pow_mem (cj_mem_O hcO) _)
  · simp only [ρOf, hs, ρL, Matrix.of_apply]
    rw [hfri, hfr]
    refine Op.mul_mem (Op.mul_mem (Op.pow_mem hcO _) ?_) (Op.pow_mem hciO _)
    rw [map_mul, map_mul]
    have hpm : ∀ k : ℕ, (D.s.atP p).ιE ((-1 : D.host.E) ^ k) ∈ Op := fun k => by
      rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _
    exact Op.mul_mem (Op.mul_mem (hpm _) (hb i j)) (hpm _)

end Good

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupFunHolds
section
noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tupFun_holds {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) : Formalism.L2.SG.Pf.FibPart.TupFun M δ u u' F0 what₂ := by
  intro hpre γ w Z hel hZ hrep
  obtain ⟨hAg, -, -, hN, hR, hE⟩ := hpre
  let Zd : LocDat D := ⟨δ, M, hAg⟩
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
      Formalism.L2.SG.PairVal.MatR D × Formalism.L2.SG.PairVal.MatR D,
      Formalism.L2.SG.PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    obtain ⟨y, hy⟩ := hN γ w hel.2 (hE γ w hel) hel.1.1
    exact ⟨(w, y), hy⟩
  have hzT : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  obtain ⟨⟨hPD₁, hmk₁⟩, hA₁, -⟩ := hex.choose_spec
  obtain ⟨F₂, hF₂, hPD₂, hmk₂⟩ := hrep
  have hRL : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  have hdc : Formalism.L2.SG.TermDef.DCRel γ.lam (lf D F0) hex.choose.2.1 F₂ :=
    (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (Formalism.L2.SG.TermDef.PD D γ.lam (lf D F0) u') ⟨_, hPD₁⟩
      ⟨F₂, hPD₂⟩).1 (hmk₁.trans hmk₂.symm)
  have hZ2 : ZhatL (lf D F0) F₂ = Z := hF₂.2.2.2.2
  funext p
  obtain ⟨l, ρ, hl, hρ, h1⟩ := one_dir Zd hRL _ F₂ hPD₁ hA₁ hF₂.2.1 hdc p
  obtain ⟨l', ρ', hl', hρ', h2⟩ := one_dir Zd hRL F₂ _ hPD₂ hF₂.2.1 hA₁
    (Formalism.L2.SG.Pf.dcrel_symm γ.lam (lf D F0) hdc) p
  have key := kkOrb_eq_of hl' hρ' hl hρ h2 h1
  show kkOrb M p (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p) =
    kkOrb M p (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p Z * sgnP p)
  rw [hzT, ← hZ2]
  exact key

end Formalism.L2.SG.Pf.FibQ
end
end

