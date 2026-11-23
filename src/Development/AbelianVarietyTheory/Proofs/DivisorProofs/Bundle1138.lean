module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCrossPowersOfPullbackPowers
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.CrossIso

variable {X Y Z : Scheme.{0}}

theorem gm_pw_g (L : LB X) (t : ℤ) (f : Y ⟶ X) (y : Y) (i j : L.ι) :
    gm f y ((GlobalTheory.AbLaw.pw L t).U i ⊓ (GlobalTheory.AbLaw.pw L t).U j) ((GlobalTheory.AbLaw.pw L t).g i j) =
      gm f y (L.U i ⊓ L.U j) (L.g i j) ^ t :=
  map_zpow (gm f y (L.U i ⊓ L.U j)) (L.g i j) t

theorem gm_pull_g (L : LB X) (F : Y ⟶ X) (f : Z ⟶ Y) (z : Z) (J J' : PUnit → L.ι)
    (hj : F (f z) ∈ L.U (J PUnit.unit)) (hj' : F (f z) ∈ L.U (J' PUnit.unit)) :
    gm f z ((L.pull F).U J ⊓ (L.pull F).U J') ((L.pull F).g J J') =
      gm (f ≫ F) z _ (L.g (J PUnit.unit) (J' PUnit.unit)) := by
  have hp : f z ∈ (L.pull F).U J ⊓ (L.pull F).U J' := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f z _ (∏ _k : PUnit, (res _ (pullU F _ (L.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f z _ hp _).trans
    (gm_pull f F z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) ⟨hj, hj'⟩ _)

theorem gw_chart {b : Y ⟶ X} {A : LB X} {N : LB Y} {p : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (hw : w.IsGen) (r : Z ⟶ Y) (z : Z) (k k' : A.ι) (l l' : N.ι) (hk : b (r z) ∈ A.U k) (hk' : b (r z) ∈ A.U k')
    (hl : r z ∈ N.U l) (hl' : r z ∈ N.U l') :
    gw w r z k l = gm (r ≫ b) z _ (A.g k k') * (gm r z _ (N.g l l') ^ p)⁻¹ * gw w r z k' l' := by
  have := (isGen_iff w).1 hw Z r z k k' l l' hk hk' hl hl'
  rw [gm_pw_g] at this
  exact this

theorem cross_alg {G : Type} [CommGroup G] (p q : ℤ) (a a' n u u' : G) :
    (a' * (n ^ q)⁻¹ * u') ^ p * ((a * (n ^ p)⁻¹ * u) ^ q)⁻¹ = a' ^ p * (a ^ q)⁻¹ * (u' ^ p * (u ^ q)⁻¹) := by
  simp only [mul_zpow, inv_zpow, ← zpow_mul, mul_comm q p, mul_inv, inv_inv]
  generalize n ^ (p * q) = m
  generalize a' ^ p = A'
  generalize a ^ q = A
  generalize u' ^ p = U'
  generalize u ^ q = U
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cross_chart {b : Y ⟶ X} {A A' : LB X} {N : LB Y} {p q : ℤ} (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b))
    (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)) (hw : w.IsGen) (hw' : w'.IsGen) (r : Z ⟶ Y) (z : Z)
    (k₁ k₂ : A.ι) (j₁ j₂ : A'.ι) (l₁ l₂ : N.ι) (hk₁ : b (r z) ∈ A.U k₁) (hk₂ : b (r z) ∈ A.U k₂)
    (hj₁ : b (r z) ∈ A'.U j₁) (hj₂ : b (r z) ∈ A'.U j₂) (hl₁ : r z ∈ N.U l₁) (hl₂ : r z ∈ N.U l₂) :
    gw w' r z j₁ l₁ ^ p * (gw w r z k₁ l₁ ^ q)⁻¹ =
      gm (r ≫ b) z _ (A'.g j₁ j₂) ^ p * (gm (r ≫ b) z _ (A.g k₁ k₂) ^ q)⁻¹ *
        (gw w' r z j₂ l₂ ^ p * (gw w r z k₂ l₂ ^ q)⁻¹) := by
  rw [gw_chart w hw r z k₁ k₂ l₁ l₂ hk₁ hk₂ hl₁ hl₂, gw_chart w' hw' r z j₁ j₂ l₁ l₂ hj₁ hj₂ hl₁ hl₂]
  exact cross_alg _ _ _ _ _ _ _

end GlobalTheory.FormalAlg.CrossIso

namespace GlobalTheory.FormalAlg
open CrossIso

theorem exists_crossIso : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  intro X Y b A A' N p q w w' hA hA' hN hw hw'
  have glue : ∀ (j : A'.ι) (k : A.ι), ∃ s : Γ(Y, ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
      ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k))ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U j → r z ∈ N.U l →
        gm r z _ s = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : N.ι → Y.Opens, ∀ l x, x ∈ W l ↔ b x ∈ A.U k ∧ b x ∈ A'.U j ∧ x ∈ N.U l :=
      ⟨fun l => b ⁻¹ᵁ A.U k ⊓ (b ⁻¹ᵁ A'.U j ⊓ N.U l), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ l, W l ≤ ((GlobalTheory.AbLaw.pw A' p).pull b).U (fun _ => j) ⊓
        ((GlobalTheory.AbLaw.pw A q).pull b).U (fun _ => k) := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, mem_pull.2 ((hW l x).1 hx).1⟩
    have l₁ : ∀ l, W l ≤ (A'.pull b).U (fun _ => j) ⊓ (GlobalTheory.AbLaw.pw N q).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).2.1, ((hW l x).1 hx).2.2⟩
    have l₂ : ∀ l, W l ≤ (A.pull b).U (fun _ => k) ⊓ (GlobalTheory.AbLaw.pw N p).U l := fun l x hx =>
      ⟨mem_pull.2 ((hW l x).1 hx).1, ((hW l x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : N.ι), r z ∈ W l →
        gm r z (W l) (u l) = gw w' r z j l ^ p * (gw w r z k l ^ q)⁻¹ :=
      ⟨fun l => res (l₁ l) (w'.s (fun _ => j, l)) ^ p * (res (l₂ l) (w.s (fun _ => k, l)) ^ q)⁻¹,
        fun Z r z l hy => (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((map_zpow _ _ _).trans (congrArg (· ^ p) (gm_res r z (l₁ l) hy _)))
          ((map_inv _ _).trans (congrArg (·⁻¹)
            ((map_zpow _ _ _).trans (congrArg (· ^ q) (gm_res r z (l₂ l) hy _))))))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨l, hl⟩ := exists_chart hN x
        exact Opens.mem_iSup.2 ⟨l, (hW l x).2 ⟨mem_pull.1 hx.2, mem_pull.1 hx.1, hl⟩⟩) u (fun l l' x hx => by
        have h₁ := (hW l x).1 hx.1
        have h₂ := (hW l' x).1 hx.2
        have e := cross_chart w w' hw hw' (𝟙 Y) x k k j j l l' h₁.1 h₁.1 h₁.2.1 h₁.2.1 h₁.2.2 h₂.2.2
        rw [gm_self hA (𝟙 Y ≫ b) x h₁.1, gm_self hA' (𝟙 Y ≫ b) x h₁.2.1, one_zpow, one_zpow, inv_one, one_mul,
          one_mul] at e
        exact (hu _ (𝟙 Y) x l hx.1).trans (e.trans (hu _ (𝟙 Y) x l' hx.2).symm))
    refine ⟨s, fun Z r z l hk hj hl => ?_⟩
    have hy := (hW l (r z)).2 ⟨hk, hj, hl⟩
    exact (gm_res r z (l₀ l) hy s).symm.trans ((congrArg (gm r z (W l)) (hs l)).trans (hu Z r z l hy))
  choose s hs using glue
  let c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b) :=
    ⟨fun P => s (P.1 PUnit.unit) (P.2 PUnit.unit)⟩
  have hc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (K : PUnit → A.ι) (j : A'.ι) (l : N.ι),
      b (r z) ∈ A.U (K PUnit.unit) → b (r z) ∈ A'.U j → r z ∈ N.U l →
      gw c r z j K = gw w' r z j l ^ p * (gw w r z (K PUnit.unit) l ^ q)⁻¹ :=
    fun Z r z K j l hk hj hl => hs j (K PUnit.unit) Z r z l hk hj hl
  refine ⟨c, (isGen_iff c).2 ?_, fun Z r z k j l hk hj hl => hc Z r z (fun _ => k) j l hk hj hl⟩
  intro Z r z j j' K K' hj hj' hK hK'
  obtain ⟨l, hl⟩ := exists_chart hN (r z)
  have hk := mem_pull.1 hK
  have hk' := mem_pull.1 hK'
  have e := cross_chart w w' hw hw' r z (K PUnit.unit) (K' PUnit.unit) j j' l l hk hk' hj hj' hl hl
  refine (hc Z r z K j l hk hj hl).trans (e.trans ?_)
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pw_g A' p _ z j j').symm (congrArg (·⁻¹) ?_))
    (hc Z r z K' j' l hk' hj' hl).symm
  exact ((gm_pull_g (GlobalTheory.AbLaw.pw A q) b r z K K' hk hk').trans (gm_pw_g A q _ z _ _)).symm

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem exists_localEqn_of_isQCart : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), ∀ (D : X → ℚ), IsQCart D → ∀ x : X, ∃ (m : ℕ) (f : X.functionFieldˣ), 0 < m ∧ RegAt x (f : X.functionField) ∧ ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m := by
  intro X _ _ p D hD x
  obtain ⟨m, D₀, hm, hEff, rfl⟩ := hD
  obtain ⟨f, hf⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hfV⟩ := hf.exists_nhds
  refine ⟨m, f, hm, CartierDiv.eff_iff.1 hEff x f hf, fun z hz E hE => ?_⟩
  rw [qWeil, (hfV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfPullbackPowerOnNonzeroLocus
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

namespace GlobalTheory.Div.FramePull

variable {X X₀ : Scheme.{0}}

theorem isUnit_res_of_le {V U : X₀.Opens} (f : Γ(X₀, U)) (h : V ≤ X₀.basicOpen f) :
    IsUnit ((X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f) := by
  have e : (X₀.presheaf.map (homOfLE (h.trans (X₀.basicOpen_le f))).op).hom f =
      (X₀.presheaf.map (homOfLE h).op).hom ((X₀.presheaf.map (homOfLE (X₀.basicOpen_le f)).op).hom f) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  rw [e]
  exact (X₀.toRingedSpace.isUnit_res_basicOpen f).map _

theorem le_basicOpen {H : LB X₀} (s : LB.Sec H) (a : H.ι) :
    nonzeroLocus s ⊓ H.U a ≤ X₀.basicOpen (s.f a) := by
  rintro z ⟨hz, ha⟩
  obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have e := congrArg X₀.basicOpen (s.compat a a')
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (H.g a a').isUnit, Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e
  have hm : z ∈ H.U a ⊓ H.U a' ⊓ X₀.basicOpen (s.f a) := by
    rw [e]; exact ⟨⟨ha, X₀.basicOpen_le _ ha'⟩, ⟨ha, X₀.basicOpen_le _ ha'⟩, ha'⟩
  exact hm.2

theorem gm_gen_div {M L' : LB X₀} {w : LB.Iso L' M} (hw : w.IsGen) (z : X₀) (p q : M.ι × L'.ι)
    (hp : z ∈ M.U p.1 ⊓ L'.U p.2) (hq : z ∈ M.U q.1 ⊓ L'.U q.2) :
    gm (𝟙 X₀) z _ (w.s p) = gm (𝟙 X₀) z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      (gm (𝟙 X₀) z (L'.U p.2 ⊓ L'.U q.2) (L'.g p.2 q.2))⁻¹ * gm (𝟙 X₀) z _ (w.s q) := by
  have hm : z ∈ (LB.div M L').U p ⊓ (LB.div M L').U q := ⟨hp, hq⟩
  have := congrArg (gm (𝟙 X₀) z _) (hw p q)
  rw [gm_res _ z _ hm, map_mul, gm_res _ z _ hm] at this
  rw [this]
  refine congrArg (· * _) ?_
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res _ z _ hm _))))

theorem gm_pull_g (L : LB X) (γ : X₀ ⟶ X) (z : X₀) (m m' : L.ι) (hm : γ z ∈ L.U m) (hm' : γ z ∈ L.U m') :
    gm (𝟙 X₀) z ((L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m'))
      ((L.pull γ).g (fun _ => m) (fun _ => m')) = gm γ z _ (L.g m m') := by
  have hp : z ∈ (L.pull γ).U (fun _ => m) ⊓ (L.pull γ).U (fun _ => m') := ⟨mem_pull.2 hm, mem_pull.2 hm'⟩
  show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g m m'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (gm_res _ z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U m ⊓ L.U m') ⟨hm, hm'⟩ _).trans ?_)
  rw [Category.id_comp]

theorem grp₁ {M : Type} [CommGroup M] (G S W : M) (k : ℕ) :
    (G * S) ^ k * (G ^ (k : ℤ) * 1⁻¹ * W)⁻¹ = S ^ k * W⁻¹ := by
  rw [zpow_natCast, inv_one, mul_one, mul_pow, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

theorem grp₂ {M : Type} [CommGroup M] (S Γ W : M) (k : ℕ) :
    S ^ k * ((1 : M) ^ (k : ℤ) * Γ⁻¹ * W)⁻¹ = Γ * (S ^ k * W⁻¹) := by
  rw [one_zpow, one_mul, mul_inv, inv_inv, mul_left_comm]

theorem frame_pull : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB →
    H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s →
    ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' →
      gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧
      ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a →
        gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  intro X X₀ γ H₀ s k L hL hH w hw D hD
  let W : L.ι → H₀.ι → X₀.Opens := fun m a => γ ⁻¹ᵁ (D ⊓ L.U m) ⊓ H₀.U a
  have hWb : ∀ m a, W m a ≤ X₀.basicOpen (s.f a) := fun m a z hz =>
    le_basicOpen s a ⟨hD ▸ (show z ∈ γ ⁻¹ᵁ D from hz.1.1), hz.2⟩
  have hWw : ∀ m a, W m a ≤ (LB.div (pw H₀ k) (L.pull γ)).U (a, fun _ => m) := fun m a z hz =>
    ⟨hz.2, mem_pull.2 hz.1.2⟩
  let S : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => (isUnit_res_of_le (s.f a) (hWb m a)).unit
  let v : ∀ m a, Γ(X₀, W m a)ˣ := fun m a => S m a ^ k * (res (hWw m a) (w.s (a, fun _ => m)))⁻¹
  have hS : ∀ m a z (hz : z ∈ W m a), (gm (𝟙 X₀) z _ (S m a)).val = gs (𝟙 X₀) z _ (s.f a) := by
    intro m a z hz
    rw [← gs_unit _ z _ hz, IsUnit.unit_spec]
    exact gs_res _ z _ hz _
  have hv : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (v m a) =
      gm (𝟙 X₀) z _ (S m a) ^ k * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m)))⁻¹ := by
    intro m a z hz
    simp only [v, map_mul, map_pow, map_inv]
    rw [gm_res _ z _ hz]

  have hwg : ∀ z a a' m m', z ∈ H₀.U a → z ∈ H₀.U a' → γ z ∈ L.U m → γ z ∈ L.U m' →
      gm (𝟙 X₀) z _ (w.s (a, fun _ => m)) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') ^ (k : ℤ) *
        (gm γ z _ (L.g m m'))⁻¹ * gm (𝟙 X₀) z _ (w.s (a', fun _ => m')) := by
    intro z a a' m m' ha ha' hm hm'
    rw [gm_gen_div hw z (a, fun _ => m) (a', fun _ => m') ⟨ha, mem_pull.2 hm⟩ ⟨ha', mem_pull.2 hm'⟩,
      gm_pull_g L γ z m m' hm hm']
    exact congrArg (fun t => t * _ * _) (map_zpow _ _ _)
  have hSg : ∀ m m' a a' z (hz : z ∈ W m a) (hz' : z ∈ W m' a'),
      gm (𝟙 X₀) z _ (S m a) = gm (𝟙 X₀) z (H₀.U a ⊓ H₀.U a') (H₀.g a a') * gm (𝟙 X₀) z _ (S m' a') := by
    intro m m' a a' z hz hz'
    apply Units.ext
    rw [Units.val_mul, hS m a z hz, hS m' a' z hz']
    exact gs_sec_chart s (𝟙 X₀) z hz.2 hz'.2
  have glue : ∀ m, ∃ t : Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, ∀ a, res (inf_le_left : W m a ≤ _) t = v m a := by
    intro m
    refine glue_unit (γ ⁻¹ᵁ (D ⊓ L.U m)) (W m) (fun a => inf_le_left) (fun z hz => ?_) (v m) ?_
    · obtain ⟨a, ha⟩ := exists_chart hH z
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, hz, ha⟩
    · intro a a' z hz
      rw [hv m a z hz.1, hv m a' z hz.2, hSg m m a a' z hz.1 hz.2,
        hwg z a a' m m hz.1.2 hz.2.2 hz.1.1.2 hz.1.1.2, gm_self hL γ z hz.1.1.2]
      exact grp₁ _ _ _ k
  choose u hu using glue
  have hug : ∀ m a z (hz : z ∈ W m a), gm (𝟙 X₀) z _ (u m) = gm (𝟙 X₀) z _ (v m a) := by
    intro m a z hz
    rw [← hu m a, gm_res _ z _ hz]
  refine ⟨u, fun z m m' hm hm' => ?_, fun z m a hm ha => ?_⟩
  · obtain ⟨a, ha⟩ := exists_chart hH z
    have hz : z ∈ W m a := ⟨hm, ha⟩
    have hz' : z ∈ W m' a := ⟨hm', ha⟩
    rw [hug m a z hz, hug m' a z hz', hv m a z hz, hv m' a z hz', hSg m m' a a z hz hz',
      gm_self hH (𝟙 X₀) z ha, one_mul, hwg z a a m m' ha ha hm.2 hm'.2, gm_self hH (𝟙 X₀) z ha]
    exact grp₂ _ _ _ k
  · have hz : z ∈ W m a := ⟨hm, ha⟩
    rw [hug m a z hz, hv m a z hz, ← hS m a z hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.Div.FramePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalModelAtComplexPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem exists_locModel_at_point :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.EssFiniteType ℂ A] (ε : A →ₐ[ℂ] ℂ),
      ∃ T : Subring (FractionRing A), IsLocModel (algebraMap ℂ (FractionRing A)) T ∧
        RatRes (algebraMap ℂ (FractionRing A)) T ∧
        ∀ a : A, algebraMap A (FractionRing A) a ∈ T ∧
          (ε a = 0 → NonUnit T (algebraMap A (FractionRing A) a)) := by
  intro A _ _ _ _ ε
  let K := FractionRing A
  let P : Ideal A := RingHom.ker (ε : A →+* ℂ)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hle : P.primeCompl ≤ nonZeroDivisors A := P.primeCompl_le_nonZeroDivisors
  let B : Subalgebra A K := Localization.subalgebra.ofField K P.primeCompl hle
  haveI hB : IsLocalization P.primeCompl B := Localization.subalgebra.isLocalization_ofField K _ hle
  let b : A →+* B := algebraMap A B
  have hu : ∀ y : P.primeCompl, IsUnit ((ε : A →+* ℂ) y) := fun y => by
    refine isUnit_iff_ne_zero.2 fun h => y.2 ?_
    exact RingHom.mem_ker.2 h
  let ψ : B →+* ℂ := IsLocalization.lift hu
  have hψ : ∀ x, ψ (b x) = ε x := IsLocalization.lift_eq hu
  have hcK : ∀ z : ℂ, algebraMap ℂ K z = algebraMap A K (algebraMap ℂ A z) :=
    fun z => IsScalarTower.algebraMap_apply ℂ A K z
  have hc : ∀ z : ℂ, algebraMap ℂ K z ∈ B.toSubring := fun z => by
    rw [hcK]; exact B.algebraMap_mem _
  have hψc : ∀ z : ℂ, ψ ⟨algebraMap ℂ K z, hc z⟩ = z := fun z => by
    have : (⟨algebraMap ℂ K z, hc z⟩ : B) = b (algebraMap ℂ A z) := Subtype.ext (hcK z)
    rw [this, hψ]; exact ε.commutes z
  have key : ∀ x : B, ψ x = 0 → NonUnit B.toSubring (x : K) := fun x hx => by
    refine (nonUnit_iff (R := B.toSubring) x).2 fun h => ?_
    have := h.map ψ
    rw [hx] at this
    exact not_isUnit_zero this
  refine ⟨B.toSubring, ⟨hc, IsLocalization.AtPrime.isLocalRing B P, ?_, ?_⟩, ?_, fun a => ?_⟩
  · have e : (algebraMap ℂ K).codRestrict B.toSubring hc = b.comp (algebraMap ℂ A) := by
      ext z; exact hcK z
    rw [e]
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra.EssFiniteType ℂ A)
    · exact (RingHom.essFiniteType_algebraMap (R := A) (S := B)).2
        (Algebra.EssFiniteType.of_isLocalization B P.primeCompl)
  · intro f
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) f
    have hy' : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, B.algebraMap_mem x, _, B.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · intro r hr
    refine ⟨ψ ⟨r, hr⟩, key (⟨r, hr⟩ - ⟨algebraMap ℂ K (ψ ⟨r, hr⟩), hc _⟩) ?_⟩
    rw [ψ.map_sub, hψc, sub_self]
  · refine ⟨B.algebraMap_mem a, fun ha => key (b a) ?_⟩
    rw [hψ, ha]

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZero
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerAbs

theorem exists_ne_zero_of_twTerm_ne_zero {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (δ : G) (f : G → ℂ) (y : G) (h : GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0) :
    ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  have hu : (fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))) = fun _ => 0 := by
    funext k
    exact hc k k.2
  unfold GlobalTheory.EulerAbs.twTerm
  rw [hu]
  simp [GlobalTheory.BCT.avg]

end GlobalTheory.EulerAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenInterEqSingletonOfNoGenerisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.exists_open_inter_eq_singleton_of_no_generisation :
    ∀ (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X] (T : Set X) (x : X), IsClosed T → IsClosed ({x} : Set X) → x ∈ T → (∀ z ∈ T, z ⤳ x → z = x) → ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, y ∈ T ↔ y = x := by
  intro X _ T x hT hx hxT hgen
  obtain ⟨S, hSf, hScl, hSirr, hTS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  let S' : Set (Set X) := {t | t ∈ S ∧ x ∉ t}
  have hS'f : S'.Finite := hSf.subset (fun t ht => ht.1)
  have hcl : IsClosed (⋃₀ S') := by
    rw [Set.sUnion_eq_biUnion]
    exact hS'f.isClosed_biUnion (fun t ht => hScl t ht.1)
  refine ⟨⟨(⋃₀ S')ᶜ, hcl.isOpen_compl⟩, ?_, ?_⟩
  · show x ∈ (⋃₀ S')ᶜ
    rintro ⟨t, ht, hxt⟩
    exact ht.2 hxt
  · intro y hy
    have hy' : y ∈ (⋃₀ S')ᶜ := hy
    constructor
    · intro hyT
      rw [hTS] at hyT
      obtain ⟨t, htS, hyt⟩ := hyT
      by_cases hxt : x ∈ t
      · have hirr := hSirr t htS
        have hclt := hScl t htS
        obtain ⟨η, hηg⟩ := QuasiSober.sober hirr hclt
        have hgp : closure ({η} : Set X) = t := hηg.def
        have hη : η ∈ t := by
          rw [← hgp]; exact subset_closure rfl
        have hηT : η ∈ T := by
          rw [hTS]; exact ⟨t, htS, hη⟩
        have hsp : η ⤳ x := by
          rw [specializes_iff_mem_closure, hgp]; exact hxt
        have heq := hgen _ hηT hsp
        rw [heq, hx.closure_eq] at hgp
        rw [← hgp] at hyt
        exact hyt
      · exact absurd (Set.mem_sUnion.mpr ⟨t, (⟨htS, hxt⟩ : t ∈ S'), hyt⟩) hy'
    · rintro rfl; exact hxT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitTorsion

theorem principal_unit_idele_torsion : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  intro E _ _ t ht hnorm
  have hv : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (t : E) ≤ 1 := by
    intro v
    have h1 := ht v
    have h2 : ((Neutral.B1.diagUnits E t : AdeleRing (𝓞 E) E)).2 v = ((t : E) : v.adicCompletion E) := rfl
    rw [h2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1.le
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (t : E) hv
  have hint : IsIntegral ℤ (t : E) := by
    rw [← hy]; exact y.isIntegral_coe
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hint hnorm
  exact ⟨n, hn, Units.ext (by simpa using hpow)⟩

end GlobalTheory.UnitTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCmFieldEqTwoMulTotallyRealSubfield
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.cm_finrank_eq_two_mul (D : D7) :
    Module.finrank ℚ D.host.E = Module.finrank ℚ D.host.F * 2 := by
  have h := (GlobalTheory.AdelicU.isCMExt_host D).2.2.1
  rw [← h]
  exact (Module.finrank_mul_finrank ℚ D.host.F D.host.E).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicDerivCompactSupportEqZeroStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_antiholomorphicDeriv_compactSupport_eq_zero : ∀ {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∀ v ∈ U, v ∉ K → g v = 0) → IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  first | exact @GlobalTheory.GoodTop.setIntegral_dbar_eq_zero | exact GlobalTheory.GoodTop.setIntegral_dbar_eq_zero | (intros; apply GlobalTheory.GoodTop.setIntegral_dbar_eq_zero <;> assumption)
end

