module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0051
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.PowEqOneOfIsFullLev
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueWeightTriangularFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaSumEqOfWitnessesCommonAlgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} (Λ : GenLat E n) (N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (w : FrPt Xo c T) (hm : FrMap ψ y w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (tp : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo y.x z)
    (ht : ∀ q b, tp q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp q b))
    (hF : ∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (tp q b) (F q i b)) :
    ∃ (z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (tp' : (Fin n → LevQ Dw l) → Fin n → (ptO Xo w.x ⟶ Xo.univ.t.G))
      (F' : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
        LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo w.x))),
      (∀ i, InZh Xo Λ N (z' i)) ∧ GeoInj Xo w.x z' ∧
      (∀ q b, tp' q b ^ N = levPt Xo w.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp' q b)) ∧
      (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N w.s (z' i b) (tp' q b) (F' q i b)) ∧
      ∀ q, ψ (∑ i, ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, nab y ((N : ℤ) ^ 2) (F q i b) (colOf m b)) =
        ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) *
          ∏ b, nab w ((N : ℤ) ^ 2) (F' q i b) (colOf m b) := by
  have hx : w.x = spMap ψ.toRingHom ≫ y.x := by
    unfold FrMap at hm
    exact hm.1
  let h : ptO Xo w.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx.symm
  have hh : h.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm h hh
  have hpull : ∀ q i b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G)
      (whiskerRight_snd _ _) (F q i b) (GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) :=
    fun q i b => GlobalTheory.VVRank.isPullSec_pullS _ _ h _
  obtain ⟨hZ, -, hG, -⟩ := _root_.GlobalTheory.inZh_geoInj_stable E H Dw l Xo n Λ N
  refine ⟨fun i b => h ≫ z i b, fun q b => h ≫ tp q b,
    fun q i b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b),
    fun i => hZ _ _ h _ (hz i), hG S T y.x w.x ψ.toRingHom h hh _ z hg, fun q b => ⟨?_, ?_⟩,
    fun q i b => (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo N ⊥ _ _ h y.s w.s hs
      (F q i b) _ (hpull q i b)).2 (z i b) (tp q b) (hF q i b), fun q => ?_⟩
  · dsimp only
    rw [← MonObj.comp_pow, (ht q b).1]
    unfold levPt
    rw [← Category.assoc, toUnit_unique (h ≫ toUnit _) (toUnit _)]
  · obtain ⟨j, hj⟩ := (ht q b).2
    refine ⟨j, ?_⟩
    unfold KilledBy at hj ⊢
    intro x hx
    rw [Category.assoc, hj x hx, MonObj.comp_one]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact _root_.GlobalTheory.harmonicValue_baseChange hC E H Dw l Xo c nab hnab S T ψ y w hm h hh a n P hP N (F q i)
        (fun b => GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) h (F q i b)) (hpull q i)

theorem eq_of_local {K T : Type} [Field K] [CommRing T] [Algebra K T] (u v : T)
    (h : ∀ (U : Type) [CommRing U] [IsLocalRing U] [Algebra K U] (κ : T →ₐ[K] U), κ u = κ v) : u = v := by
  rw [← sub_eq_zero]
  refine eq_zero_of_localization (u - v) fun J hJ => ?_
  have := hJ.isPrime
  have e := h (Localization.AtPrime J) (IsScalarTower.toAlgHom K T (Localization.AtPrime J))
  simpa [map_sub, sub_eq_zero] using e

theorem shortSum_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y1.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y2.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → FrMap φ2 y y2 → (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y1.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y1.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y1.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y2.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y2.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y2.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ∀ q, ψ1 (∑ i, ∑ m ∈ P.support, algebraMap c.F S1 (P.coeff m) * ∏ b, nab y1 ((N : ℤ) ^ 2) (F1 q i b) (colOf m b)) = ψ2 (∑ i, ∑ m ∈ P.support, algebraMap c.F S2 (P.coeff m) * ∏ b, nab y2 ((N : ℤ) ^ 2) (F2 q i b) (colOf m b)) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab n Λ N hUn hTr hLev a P hP S _ _ y S1 _ _ φ1 y1 z1 tp1 F1
    S2 _ _ φ2 y2 z2 tp2 F2 hm1 hm2 hz1 hg1 ht1 hF1 hz2 hg2 ht2 hF2 T _ _ ψ1 ψ2 hψ q
  refine eq_of_local (K := c.F) _ _ fun U _ _ _ κ => ?_
  obtain ⟨yU, hyU⟩ := _root_.GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c S U ((κ.comp ψ1).comp φ1) y
  have e : (κ.comp ψ1).comp φ1 = (κ.comp ψ2).comp φ2 := by
    rw [AlgHom.comp_assoc, AlgHom.comp_assoc, hψ]
  have hU1 : FrMap (κ.comp ψ1) y1 yU := GlobalTheory.FramedBaseChange.cancel φ1 (κ.comp ψ1) hm1 hyU
  have hU2 : FrMap (κ.comp ψ2) y2 yU := GlobalTheory.FramedBaseChange.cancel φ2 (κ.comp ψ2) hm2 (e ▸ hyU)
  obtain ⟨z1', tp1', F1', hz1', hg1', ht1', hF1', hs1⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ1) y1 yU hU1 z1 tp1 F1 hz1 hg1 ht1 hF1
  obtain ⟨z2', tp2', F2', hz2', hg2', ht2', hF2', hs2⟩ :=
    exists_pull hC nab hnab Λ N a P hP (κ.comp ψ2) y2 yU hU2 z2 tp2 F2 hz2 hg2 ht2 hF2
  have key := _root_.GlobalTheory.shortSum_indep_local hL E H Dw l Xo c nab hnab n Λ N hUn hTr hLev P U yU z1' tp1' F1' z2' tp2' F2'
    hz1' hg1' ht1' hF1' hz2' hg2' ht2' hF2' q
  have h1 := hs1 q
  have h2 := hs2 q
  simp only [AlgHom.comp_apply] at h1 h2
  rw [h1, h2]
  exact key

end GlobalTheory.ShortCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNullValueExistsUniqueNaturalLinear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NullValue

section Val

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] (L : LB A.left) (a : ℤ)

theorem isValueAt_congr {T : Over X} {s : LB.Sec (LPow A L a T)} {z z' : T ⟶ A} (e : z = z')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))}
    {τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z'.left) (fun _ => a))}
    (hτ : ∀ (j : Fin 1 → L.ι) (y : T.left), y ∈ LB.wchart L (fun _ : Fin 1 => z.left) j →
      y ∈ LB.wchart L (fun _ : Fin 1 => z'.left) j → gm (𝟙 _) y _ (τ.s j) = gm (𝟙 _) y _ (τ'.s j))
    {v : Γ(T.left, ⊤)} (h : IsValueAt A L a s z τ v) : IsValueAt A L a s z' τ' v := by
  subst e
  have hU : ∀ j, (τ.s j).val = (τ'.s j).val := by
    intro j
    apply TopCat.Presheaf.section_ext T.left.sheaf
    intro y hy
    have hyU : (𝟙 T.left : T.left ⟶ T.left) y ∈ (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := hy
    have key := hτ j y hy hy
    clear hτ h
    unfold gm at key
    rw [dite_eq_left hyU] at key
    have key2 := congrArg Units.val key
    simp only [MonoidHom.comp_apply] at key2
    unfold pullU at key2
    simp only [Units.coe_map, MonoidHom.coe_coe] at key2
    exact key2
  unfold IsValueAt at h ⊢
  intro j
  rw [← hU j]
  exact h j

private lemma gm_id_eq_germ_map {Y : Scheme.{0}} {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V)
    (x : Γ(Y, U)ˣ) :
    ((gm (𝟙 Y) y U x : (Y.presheaf.stalk y)ˣ) : Y.presheaf.stalk y) =
      Y.presheaf.germ V y hy ((Y.presheaf.map (homOfLE hVU).op).hom (x : Γ(Y, U))) := by
  unfold gm
  rw [dite_eq_left (show (𝟙 Y : Y ⟶ Y) y ∈ U from hVU hy)]
  simp only [MonoidHom.comp_apply]
  unfold pullU
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [Y.presheaf.germ_res_apply]
  rfl

private lemma gm_id_eq_of_units_map_eq {Y : Scheme.{0}} {U₁ U₂ V : Y.Opens} (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (x₁ : Γ(Y, U₁)ˣ)
    (x₂ : Γ(Y, U₂)ˣ) (y : Y) (hy : y ∈ V)
    (e : Units.map ((Y.presheaf.map (homOfLE h₁).op).hom : Γ(Y, U₁) →* Γ(Y, V)) x₁ =
      Units.map ((Y.presheaf.map (homOfLE h₂).op).hom : Γ(Y, U₂) →* Γ(Y, V)) x₂) :
    gm (𝟙 Y) y U₁ x₁ = gm (𝟙 Y) y U₂ x₂ := by
  apply Units.ext
  rw [gm_id_eq_germ_map h₁ y hy, gm_id_eq_germ_map h₂ y hy]
  have e2 := congrArg Units.val e
  simp only [Units.coe_map, MonoidHom.coe_coe] at e2
  rw [e2]

theorem isValueAt_one_pull (ρ : LB.Gen (L.pull (eSec A))) {T T' : Over X} (g : T' ⟶ T)
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s') {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s 1 (rigT A L ρ T a) v) :
    IsValueAt A L a s' 1 (rigT A L ρ T' a) (g.left.appTop.hom v) := by
  have h1 := Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.isValueAt_pull A L a g 1 hs hv
  have hc := Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull.corr_rigT_pull A L ρ g a
  have e : g ≫ (1 : T ⟶ A) = 1 := by simp
  refine isValueAt_congr A L a e ?_ h1
  intro j y hy hy'
  unfold LB.Gen.Corr at hc
  have key := hc j j (fun k₁ k₂ _ => by rw [Subsingleton.elim k₁ k₂])
    (fun k₁ k₂ _ => by rw [Subsingleton.elim k₁ k₂]) (fun k k' _ => by rw [Subsingleton.elim k k'])
  unfold res at key
  refine gm_id_eq_of_units_map_eq _ _ _ _ y ?_ key
  exact ⟨hy, hy'⟩

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem baseChange {N : ℕ} {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (ψ : S →ₐ[c.F] T) {y : FrPt Xo c S} {z : FrPt Xo c T} (hm : FrMap ψ y z)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G) (hp : p'.left = spMap ψ.toRingHom ≫ p.left)
    {w : S} (hw : IsNullVal Xo c N y p w) : IsNullVal Xo c N z p' (ψ w) := by
  obtain ⟨F, hVt, hV⟩ := hw
  have hx : spMap ψ.toRingHom ≫ y.x = z.x := by
    unfold FrMap at hm
    exact hm.1.symm
  let g : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx
  have hg : g.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm g hg
  have hF := GlobalTheory.VVRank.isPullSec_pullS (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) ((N : ℤ) ^ 2) g F
  have hpg : p' = g ≫ p := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hg]
    exact hp
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  unfold IsNullVal
  refine ⟨GlobalTheory.VVRank.pullS Xo.univ.t.G ((N : ℤ) ^ 2) g F, ?_, ?_⟩
  · unfold IsVtOver at hVt ⊢
    obtain ⟨t', α₀, α, s₁, U, ht', hok, g₀, hnm, cα, tw, hsym, hact⟩ := hVt
    have hok' : t' = p := hok
    obtain ⟨α', cα', tw'⟩ := GlobalTheory.VtBaseChange.exists_mulTwist Xo.univ.t.G hL N g hs g₀ cα tw
    obtain ⟨θ', -, -, hsymP, hactP⟩ :=
      GlobalTheory.ThetaPullback.exists_thetaGrp_pullback _ Xo.univ.t.G Xo.univ.t.PP.L hL ((N : ℤ) ^ 2) _ _ g U
    refine ⟨g ≫ t', α₀, α', _, θ', ?_, ?_, g₀, hnm, cα', tw', hsymP _ _ hsym,
      hactP _ _ _ _ hact (GlobalTheory.VVRank.isPullSec_pullS (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) _ g s₁) hF⟩
    · rw [hpg, hok']
    · show g ≫ t' = p'
      rw [hpg, hok']
  · have h1 := isValueAt_one_pull Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Xo.univ.t.PP.rig g hF hV
    have e2 : g.left.appTop.hom (toΓ S w) = toΓ T (ψ w) := GlobalTheory.NabLinear.appTop_toΓ ψ.toRingHom w
    rw [e2] at h1
    exact h1


open GlobalTheory.ThetaValueWeight in
theorem triangular {N : ℕ} {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} {t : Ix Dw → Sˣ}
    (hb : FrBor t y y') (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G) (hp : p'.left = p.left)
    {w : S} (hw : IsNullVal Xo c N y p w) : IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  have hxx : y'.x = y.x := by
    unfold FrBor at hb
    exact hb.1
  obtain ⟨d, rfl⟩ := GlobalTheory.ThetaValueWeight.exists_reframe y y' hxx
  have hpp : p' = p := Over.OverMorphism.ext hp
  subst hpp
  obtain ⟨F, hVt, hV⟩ := hw
  have hgen := fun i => GlobalTheory.ThetaValueWeight.gen_eq d hb i
  unfold IsNullVal
  refine ⟨scaleSec Xo.univ.t.G (toΓ S (t none : S)) F, ?_, ?_⟩
  · exact isVtOver_scale Xo.univ.t.G Xo.univ.t.PP (T := ptO Xo y.x) (s := y.s) (s₀ := d.s)
      (toΓ S (t none : S)) (fun j => hgen j) hVt
  · have h1 := GlobalTheory.NabLinear.isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (𝟙 (ptO Xo y.x))
      (F := F) (F' := scaleSec Xo.univ.t.G (toΓ S (t none : S)) F) (r := toΓ S (t none : S)) (fun _ => rfl)
      (isPullSec_id Xo.univ.t.G F) (isPullSec_id Xo.univ.t.G _) hV
    convert h1 using 1
    rw [map_mul]
    rfl

end GlobalTheory.NullValue

namespace GlobalTheory

theorem nullValue_existsUnique_natural_linear : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (N : ℕ), Odd N → (∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (p : ptO Xo y.x ⟶ Xo.univ.t.G), p ^ (N ^ 2) = 1 → ∃! w, IsNullVal Xo c N y p w) ∧ (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap ψ y z → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo z.x ⟶ Xo.univ.t.G), p'.left = spMap ψ.toRingHom ≫ p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N z p' (ψ w)) ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (t : Ix Dw → Sˣ), FrBor t y y' → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (p' : ptO Xo y'.x ⟶ Xo.univ.t.G), p'.left = p.left → ∀ w, IsNullVal Xo c N y p w → IsNullVal Xo c N y' p' ((t none : Sˣ) * w) := by
  intro hL E _ _ _ H Dw l Xo c N hN
  refine ⟨?_, ?_, ?_⟩
  · intro S _ _ y p hp
    obtain ⟨w, hw⟩ := GlobalTheory.EtaForm.Model.exists_isNullVal Xo c hL hN y p hp
    exact ⟨w, hw, fun w' hw' => GlobalTheory.EtaForm.Model.isNullVal_unique Xo c hL hN y p hp hw' hw⟩
  · intro S T _ _ _ _ ψ y z hm p p' hp w hw
    exact NullValue.baseChange ψ hm p p' hp hw
  · intro S _ _ y y' t hb p p' hp w hw
    exact NullValue.triangular hb p p' hp hw

end GlobalTheory
end
end

