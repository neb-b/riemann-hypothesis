module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsSymplecticFamilySpan
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameThinAffineBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResPullURes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsSquareZeroPresentedScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointPowEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MultTorsion

theorem linComb_eq_prod {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

theorem linComb_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) (m : ℕ) : linComb y a ^ m = linComb y (fun i => a i * m) := by
  rw [linComb_eq_prod, linComb_eq_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => (pow_mul _ _ _).symm

theorem linComb_mod {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n M : ℕ}
    (y : Fin n → (T ⟶ A)) (hy : ∀ i, y i ^ M = 1) (a : Fin n → ℕ) :
    linComb y a = linComb y (fun i => a i % M) := by
  rw [linComb_eq_prod, linComb_eq_prod]
  exact Finset.prod_congr rfl fun i _ => pow_eq_pow_mod _ (hy i)

theorem linComb_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) : linComb y (fun _ => 0) = 1 := by
  rw [linComb_eq_prod]; simp

end GlobalTheory.MultTorsion

namespace GlobalTheory


open MultTorsion in
theorem exists_levelPoint_pow_eq : ∀ (K : Type) [Field K] [IsAlgClosed K] (Q : PolAV (Sp K)) (m g : ℕ) (hg : Q.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Level Q (m ^ 2) ze) (z : baseOver (Sp K) ⟶ Q.A), 0 < m → z ^ m = 1 → ∃ a : Fin (2 * g) → ZMod (m ^ 2), GlobalTheory.levelPoint lev hg a ^ m = z := by
  intro K _ _ Q m g hg ze lev z hm hz
  subst hg
  have := Q.isAb.comm
  have E : ∀ c : Fin (2 * Q.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have hz2 : z ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hz, one_pow]
  obtain ⟨c, hc⟩ := lev.span K (𝟙 _) z hz2
  replace hc : linComb lev.pt (fun i => (c i : ℕ)) = z := (E _).symm.trans hc
  have hM : 0 < m ^ 2 := pow_pos hm 2
  have h1 : linComb lev.pt (fun i => (c i : ℕ) * m % (m ^ 2)) = linComb lev.pt (fun _ => 0) := by
    rw [← linComb_mod _ lev.torsion, ← linComb_pow, hc, hz, linComb_zero]
  have h2 := lev.indep K (𝟙 _) (fun i => ⟨(c i : ℕ) * m % (m ^ 2), Nat.mod_lt _ hM⟩) (fun _ => ⟨0, hM⟩)
    ((E _).trans (h1.trans (E _).symm))
  have hd : ∀ i, m ∣ (c i : ℕ) := fun i => by
    have h3 := congrArg Fin.val (congrFun h2 i)
    simp only at h3
    have h4 : m * m ∣ (c i : ℕ) * m := by rw [← sq]; exact Nat.dvd_of_mod_eq_zero h3
    exact Nat.dvd_of_mul_dvd_mul_right hm h4
  refine ⟨fun i => (((c i : ℕ) / m : ℕ) : ZMod (m ^ 2)), ?_⟩
  rw [ThetaPtDet.levelPoint_eq, levelBasis_rfl, linComb_pow, ← hc]
  refine congrArg (linComb lev.pt) (funext fun i => ?_)
  have hlt : (c i : ℕ) / m < m ^ 2 := lt_of_le_of_lt (Nat.div_le_self _ _) (c i).isLt
  rw [ZMod.val_natCast_of_lt hlt, Nat.div_mul_cancel (hd i)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureGeometricFibrePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibLevel

theorem comp_pow_pt {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem exists_level_of_pullback : ∀ (T K : Type) [CommRing T] [IsNoetherianRing T] [Field K] [IsAlgClosed K] (χ : T →+* K) (P : PolAV (Sp T)) (Q : PolAV (Sp K)) (ψ : Q.A.left ⟶ P.A.left), IsGrpPullback Q.A P.A (spMap χ) ψ → LBIso Q.L (P.L.pull ψ) → ∀ (g M : ℕ) (hg : Q.g = g) (c : Tˣ) (ζK : Kˣ), (M : K) ≠ 0 → Units.map χ.toMonoidHom c = ζK → IsPrimitiveRoot ζK M → ∀ (y : Fin (2 * g) → (baseOver (Sp T) ⟶ P.A)), (∀ i, y i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (y i) (y j) (unitOn c ^ stdSymp g i j)) → ∃ lev : Level Q M (unitOn ζK), ∀ i, (GlobalTheory.levelBasis lev hg i).left ≫ ψ = spMap χ ≫ (y i).left := by
  intro T K _ _ _ _ χ P Q ψ hpb hLB g M hg c ζK hM hcζ hζ y hy hw
  have hL : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hpb (𝟙 (Sp K)) (spMap χ) (Category.id_comp _).symm
  let h0 : Over.mk (spMap χ) ⟶ baseOver (Sp T) := Over.homMk (spMap χ) (Category.comp_id _)
  let x : Fin (2 * g) → (baseOver (Sp K) ⟶ Q.A) := fun i => e.symm (h0 ≫ y i)
  have hex : ∀ i, e (x i) = h0 ≫ y i := fun i => e.apply_symm_apply _
  have hxl : ∀ i, (h0 ≫ y i).left = (x i).left ≫ ψ := fun i => by rw [← hex, he]
  have hxM : ∀ i, x i ^ M = 1 := fun i => by
    show e.symm (h0 ≫ y i) ^ M = 1
    rw [← map_pow, ← comp_pow_pt, hy, MonObj.comp_one, map_one]
  have hv : ∀ n : ℤ, Units.map h0.left.appTop.hom.toMonoidHom (unitOn c ^ n) = unitOn ζK ^ n := by
    intro n
    rw [map_zpow]
    congr 1
    rw [← hcζ]
    apply Units.ext
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ)
    exact (congrArg (fun f => f.hom c.val) this).symm
  have key : ∀ (s : Sp K ⟶ Sp T) (_ : s = 𝟙 _ ≫ spMap χ) (x y : baseOver (Sp K) ⟶ Q.A)
      (x₀ y₀ : Over.mk s ⟶ P.A) (u : Γ(Sp K, ⊤)ˣ), x₀.left = x.left ≫ ψ → y₀.left = y.left ≫ ψ →
      WeilIs P.A P.L M x₀ y₀ u → WeilIs Q.A Q.L M x y u := by
    rintro s rfl x y x₀ y₀ u hx hy h
    have := Q.isAb.comm
    exact (weilIs_grpPullback_of_comm' _ _ _ _ _ ψ _ _ P.isLB Q.isLB hpb hLB (baseOver _) M x y x₀ y₀ u
      hx hy).2 h
  have hxp : ∀ i j, WeilIs Q.A Q.L M (x i) (x j) (unitOn ζK ^ stdSymp g i j) := fun i j => by
    have w := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h0 (hw i j)
    rw [hv] at w
    exact key _ (Category.id_comp _).symm _ _ _ _ _ (hxl i) (hxl j) w
  obtain ⟨lev, hlev⟩ := GlobalTheory.Ex.FibIso.exists_level hL Q hg hM hζ x hxM hxp
  exact ⟨lev, fun i => by rw [hlev]; exact (hxl i).symm⟩

end GlobalTheory.Mum.FibLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaDescentLevel

theorem isThetaPt_reindex {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) :
    IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

theorem exists_level : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n J : ℕ), n.Prime → 1 ≤ J → ∀ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ J) ^ 2) = 1 → ∃ i, x i = z) → IsThetaPt A (n ^ J) x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (ζ : Fˣ) (lev : Level A ((n ^ J) ^ 2) (unitOn (Units.map em.toMonoidHom ζ))) (v' : (Fin (2 * A.g) → ZMod ((n ^ J) ^ 2)) → F), IsPrimitiveRoot ζ ((n ^ J) ^ 2) ∧ IsThetaPt A (n ^ J) (GlobalTheory.levelPoint lev rfl) (fun a => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v' a))) := by
  intro F Ω _ _ _ _ _ em A n J hn _ Ix x v hx hv
  have hF : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne_zero
  have hΩ : (n : Ω) ≠ 0 := by
    rw [← map_natCast em]
    exact (map_ne_zero _).2 hF
  have hlev := nonempty_level_prime_pow GlobalTheory.abelianSchemeLaws_all.1 Ω A n (J * 2) hn hΩ
  rw [pow_mul] at hlev
  have hM : (n ^ J) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)
  generalize n ^ J = m at *
  have : NeZero (m ^ 2) := ⟨hM⟩
  have : NeZero ((m ^ 2 : ℕ) : F) := ⟨Nat.cast_ne_zero.2 hM⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).symm.commRingCatIsoToRingEquiv.injective
  have hζ' : IsPrimitiveRoot (Units.map em.toMonoidHom ζ) (m ^ 2) :=
    hζ.map_of_injective (Units.map_injective em.injective)
  obtain ⟨lev⟩ := hlev (unitOn (Units.map em.toMonoidHom ζ)) (hζ'.map_of_injective (Units.map_injective inj))
  choose i hi using fun a => hx _ (ThetaPtDet.levelPoint_pow lev rfl a)
  refine ⟨ζ, lev, fun a => v (i a), hζ, ?_⟩
  have h := isThetaPt_reindex hv i
  rwa [show (fun a => x (i a)) = GlobalTheory.levelPoint lev rfl from funext hi] at h

end GlobalTheory.ThetaDescentLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentBijectiveApp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.LBDesc

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext glue_unit exists_chart gw PGen)

variable {Z Y : Scheme.{0}}

def toZ (V : Z.Opens) {O : V.toScheme.Opens} (a : Γ(V.toScheme, O)ˣ) : Γ(Z, V.ι ''ᵁ O)ˣ := a

theorem toZ_res (V : Z.Opens) {O O' : V.toScheme.Opens} (h : O' ≤ O) (a : Γ(V.toScheme, O)ˣ) :
    toZ V (res h a) = res (V.ι.image_mono h) (toZ V a) := rfl

theorem toZ_mul (V : Z.Opens) {O : V.toScheme.Opens} (a b : Γ(V.toScheme, O)ˣ) :
    toZ V (a * b) = toZ V a * toZ V b := rfl

theorem image_preimage_le' (V : Z.Opens) (O : Z.Opens) : V.ι ''ᵁ V.ι ⁻¹ᵁ O ≤ O :=
  Set.image_preimage_subset _ _

theorem toZ_pullU (V : Z.Opens) (O : Z.Opens) (a : Γ(Z, O)ˣ) :
    toZ V (pullU V.ι O a) = res (image_preimage_le' V O) a := rfl

theorem res_toZ_pullU (V : Z.Opens) (O : Z.Opens) {W : Z.Opens} (hW : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ O) (a : Γ(Z, O)ˣ) :
    res hW (toZ V (pullU V.ι O a)) = res (hW.trans (image_preimage_le' V O)) a := by
  rw [toZ_pullU, LB.res_res]

theorem transport (L' : LB Z) (V : Z.Opens) (t : LB.Gen (L'.pull V.ι)) (ht : t.IsGen) :
    ∃ T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ, ∀ k k',
      res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k') := by
  have hle : ∀ k, V ⊓ L'.U k ≤ V.ι ''ᵁ LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) := by
    intro k z hz
    exact ⟨⟨z, hz.1⟩, Set.mem_iInter.2 fun _ => hz.2, rfl⟩
  refine ⟨fun k => res (hle k) (toZ V (LB.ts t (fun _ => k))), fun k k' => ?_⟩
  have hle2 : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V.ι ''ᵁ (LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k) ⊓
      LB.wchart L' (fun _ : PUnit => V.ι) (fun _ => k')) := fun z hz =>
    ⟨⟨z, hz.1.1⟩, ⟨Set.mem_iInter.2 fun _ => hz.1.2, Set.mem_iInter.2 fun _ => hz.2.2⟩, rfl⟩
  have e := congrArg (fun x => res hle2 (toZ V x)) ((LB.isGen_iff L' t).1 ht (fun _ => k) (fun _ => k'))
  simp only [toZ_mul, toZ_res, map_mul, LB.res_res, LB.lcg, Fintype.prod_unique, zpow_one, res_toZ_pullU] at e
  simp only [LB.res_res]
  exact e

theorem gm_compat (L' : LB Z) (V : Z.Opens) (T : ∀ k : L'.ι, Γ(Z, V ⊓ L'.U k)ˣ)
    (hT : ∀ k k', res (inf_le_left : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k) (T k) =
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
        res (inf_le_right : V ⊓ L'.U k ⊓ (V ⊓ L'.U k') ≤ V ⊓ L'.U k') (T k'))
    {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι) (hV : f w ∈ V) (hk : f w ∈ L'.U k)
    (hk' : f w ∈ L'.U k') :
    gm f w (V ⊓ L'.U k) (T k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w (V ⊓ L'.U k') (T k') := by
  have hm : f w ∈ V ⊓ L'.U k ⊓ (V ⊓ L'.U k') := ⟨⟨hV, hk⟩, hV, hk'⟩
  have e := congrArg (gm f w (V ⊓ L'.U k ⊓ (V ⊓ L'.U k'))) (hT k k')
  rwa [map_mul, gm_res f w _ hm, gm_res f w _ hm, gm_res f w _ hm] at e

theorem ratio (p : Z ⟶ Y) (L' : LB Z) (hL' : L'.IsLB) {V₁ V₂ : Y.Opens}
    (T₁ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₁ ⊓ L'.U k)ˣ) (T₂ : ∀ k : L'.ι, Γ(Z, p ⁻¹ᵁ V₂ ⊓ L'.U k)ˣ)
    (h₁ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₁ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₁ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₁ k'))
    (h₂ : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V₂ → f w ∈ L'.U k → f w ∈ L'.U k' →
      gm f w _ (T₂ k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T₂ k')) :
    ∃ r : Γ(Z, p ⁻¹ᵁ (V₁ ⊓ V₂))ˣ, ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι),
      f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) → f w ∈ L'.U k → gm f w _ r = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
  have l₁ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₁ ⊓ L'.U k := fun _ x hx => ⟨hx.1.1, hx.2⟩
  have l₂ : ∀ k, p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k ≤ p ⁻¹ᵁ V₂ ⊓ L'.U k := fun _ x hx => ⟨hx.1.2, hx.2⟩
  have hu : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k : L'.ι) (hw : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k),
      gm f w _ (res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹) = gm f w _ (T₂ k) * (gm f w _ (T₁ k))⁻¹ := by
    intro W f w k hw
    rw [map_mul, map_inv, gm_res f w _ hw, gm_res f w _ hw]
  obtain ⟨s, hs⟩ := glue_unit (p ⁻¹ᵁ (V₁ ⊓ V₂)) (fun k => p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k) (fun _ => inf_le_left)
    (fun x hx => by
      obtain ⟨k, hk⟩ := exists_chart hL' x
      exact Opens.mem_iSup.2 ⟨k, hx, hk⟩)
    (fun k => res (l₂ k) (T₂ k) * (res (l₁ k) (T₁ k))⁻¹)
    (fun i j x hx => by
      rw [hu (𝟙 Z) x i hx.1, hu (𝟙 Z) x j hx.2, h₁ (𝟙 Z) x i j hx.1.1.1 hx.1.2 hx.2.2,
        h₂ (𝟙 Z) x i j hx.1.1.2 hx.1.2 hx.2.2, mul_inv, _root_.mul_mul_mul_comm, _root_.mul_inv_cancel, _root_.one_mul])
  refine ⟨s, fun f w k hw hk => ?_⟩
  have hm : f w ∈ p ⁻¹ᵁ (V₁ ⊓ V₂) ⊓ L'.U k := ⟨hw, hk⟩
  rw [← gm_res f w inf_le_left hm s, hs k, hu f w k hm]

theorem descend (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (O : Y.Opens)
    (r : Γ(Z, p ⁻¹ᵁ O)ˣ) : ∃ g : Γ(Y, O)ˣ, pullU p O g = r := by
  let e := RingEquiv.ofBijective (p.app O).hom (hp O)
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom r, Units.ext ?_⟩
  exact e.apply_symm_apply r.val

theorem eq_of_gm (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) {O : Y.Opens}
    {a b : Γ(Y, O)ˣ} (h : ∀ z : Z, p z ∈ O → gm (𝟙 Z ≫ p) z O a = gm (𝟙 Z ≫ p) z O b) : a = b := by
  have e : pullU p O a = pullU p O b := unit_ext fun z hz => by
    rw [gm_pull (𝟙 Z) p z O hz a, gm_pull (𝟙 Z) p z O hz b]
    exact h z hz
  exact Units.ext ((hp O).1 (congrArg Units.val e))

def descLB (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB Y := ⟨Y, V, g⟩

theorem isLB_descLB (p : Z ⟶ Y) (hp : ∀ V : Y.Opens, Function.Bijective (p.app V).hom) (L' : LB Z) (hL' : L'.IsLB)
    (V : Y → Y.Opens) (hyV : ∀ y, y ∈ V y) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descLB V g).IsLB := {
  cover := eq_top_iff.2 fun y _ => Opens.mem_iSup.2 ⟨y, hyV y⟩
  g_self := fun y => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [gm_res (𝟙 Z ≫ p) z _ hz, map_one]
    exact (key (𝟙 Z) z y y k hz hz hk).trans (mul_inv_cancel _)
  cocycle := fun a b c => eq_of_gm p hp fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hL' z
    rw [map_mul, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz, gm_res (𝟙 Z ≫ p) z _ hz,
      key (𝟙 Z) z a b k hz.1.1 hz.1.2 hk, key (𝟙 Z) z b c k hz.1.2 hz.2 hk,
      key (𝟙 Z) z a c k hz.1.1 hz.2 hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel }

theorem chart_le (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (q : (LB.div ((descLB V g).pull p) L').ι) :
    (LB.div ((descLB V g).pull p) L').U q ≤ p ⁻¹ᵁ V (q.1 PUnit.unit) ⊓ L'.U q.2 :=
  fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, hx.2⟩

def descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) : LB.Iso L' ((descLB V g).pull p) :=
  ⟨fun q => (res (chart_le p L' V g q) (T (q.1 PUnit.unit) q.2))⁻¹⟩

theorem gw_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ) {W : Scheme.{0}} (f : W ⟶ Z) (x : W) (j : Y) (k : L'.ι)
    (hj : p (f x) ∈ V j) (hk : f x ∈ L'.U k) :
    gw (descIso p L' V T g) f x j k = (gm f x _ (T j k))⁻¹ := by
  unfold gw descIso
  exact (map_inv (gm f x _) _).trans (congrArg (·⁻¹) (gm_res f x (chart_le p L' V g (fun _ => j, k))
    ⟨Set.mem_iInter.2 fun _ => hj, hk⟩ (T j k)))

theorem isGen_descIso (p : Z ⟶ Y) (L' : LB Z) (V : Y → Y.Opens) (T : ∀ (y : Y) (k : L'.ι), Γ(Z, p ⁻¹ᵁ V y ⊓ L'.U k)ˣ)
    (g : ∀ y y', Γ(Y, V y ⊓ V y')ˣ)
    (hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k'))
    (key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹) :
    (descIso p L' V T g).IsGen := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff]
  intro W f x j j' k k' hj hj' hk hk'
  rw [gw_descIso p L' V T g f x j k hj hk, gw_descIso p L' V T g f x j' k' hj' hk',
    key f x j j' k hj hj' hk, hc j' f x k k' hj' hk hk']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.Mum.LBDesc

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_pull)
open GlobalTheory.Mum.LBDesc

theorem lb_descend : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, Function.Bijective (p.app V).hom) →
    ∀ L' : LB Z, L'.IsLB → (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen) →
    ∃ L : LB Y, L.IsLB ∧ LBIso L' (L.pull p) := by
  intro Z Y p hp L' hL' hloc
  choose V hyV t ht using hloc
  choose T hT using fun y => transport L' (p ⁻¹ᵁ V y) (t y) (ht y)
  have hc : ∀ (y : Y) {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (k k' : L'.ι), f w ∈ p ⁻¹ᵁ V y → f w ∈ L'.U k →
      f w ∈ L'.U k' → gm f w _ (T y k) = gm f w (L'.U k ⊓ L'.U k') (L'.g k k') * gm f w _ (T y k') :=
    fun y _ f w k k' h hk hk' => gm_compat L' _ (T y) (hT y) f w k k' h hk hk'
  choose r hr using fun y y' => ratio p L' hL' (T y) (T y') (hc y) (hc y')
  choose g hg using fun y y' => descend p hp _ (r y y')
  have key : ∀ {W : Scheme.{0}} (f : W ⟶ Z) (w : W) (y y' : Y) (k : L'.ι), p (f w) ∈ V y → p (f w) ∈ V y' →
      f w ∈ L'.U k → gm (f ≫ p) w ((descLB V g).U y ⊓ (descLB V g).U y') ((descLB V g).g y y') =
        gm f w _ (T y' k) * (gm f w _ (T y k))⁻¹ := by
    intro W f w y y' k h1 h2 hk
    exact (gm_pull f p w (V y ⊓ V y') ⟨h1, h2⟩ (g y y')).symm.trans
      ((congrArg _ (hg y y')).trans (hr y y' f w k ⟨h1, h2⟩ hk))
  exact ⟨descLB V g, isLB_descLB p hp L' hL' V hyV T g key, descIso p L' V T g,
    isGen_descIso p L' V T g hc key⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftObstruction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs.ObEx

theorem exists_isObL : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀), L.IsLB → ∃ c, IsObL S α L c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S L hL
  obtain ⟨C, _, _, G, u, hB, hF⟩ := _root_.GlobalTheory.LBFrameEx.exists_frame X₀ L hL
  have hc := _root_.GlobalTheory.LBObs.FrameCoc.isCoc_of_isFrame X₀ C (opOf G) (opOf_le G) L u hL hF
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.LBObs.exists_isObU R R₀ I hI π hπ hk R₁ α C (G ⋙ OAff s₀) ((ofSys S).restrict G) u
    ((ofSys_isFun S).restrict G) (fun T T' T'' a b ↦ congrArg Units.val (hc a b))
  obtain ⟨c, rfl⟩ := (_root_.GlobalTheory.Obs.BasisExt.restrict_ext_bijective R₀ R₁ X₀ s₀ C G hB.1 hB.2).2.2 d
  exact ⟨c, C, inferInstance, inferInstance, G, hB, u, hF, hd⟩

end GlobalTheory.LBObs.ObEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LBObs.exists_lift_of_isObL_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ S X s i P L₀ hpb hL₀ hob
  obtain ⟨C', _, _, G, hbas, u, hfr, hobu⟩ := hob
  rw [map_zero] at hobu
  obtain ⟨v, hvp, hvc⟩ := _root_.GlobalTheory.LBLift.lift_of_isObU_zero R R₀ I hI π hπ hk R₁ α C' (G ⋙ OAff s₀) ((ofSys S).restrict G) u hobu
  obtain ⟨V, hV, hi, e, hpre, he, hred⟩ := _root_.GlobalTheory.PresCharts.exists_charts R R₀ I hI π hπ hk X₀ s₀ S X s i P hpb
  let V' : C' → X.Opens := fun T => V (G.obj T)
  have hV' : ∀ ⦃T T' : C'⦄, (T ⟶ T') → V' T' ≤ V' T := fun T T' a => hV (G.map a)
  let u' : ∀ (T T' : C') (_ : T ⟶ T'), Γ(X, V' T')ˣ := fun T T' a => Units.map (e (G.obj T')).toMonoidHom (v T T' a)
  have hcoc : IsCoc V' hV' u' := by
    intro T T' T'' a b
    ext
    have h1 := hvc T T' T'' a b
    change e (G.obj T'') (v T T'' (a ≫ b)).val = _
    rw [h1]
    refine ((e (G.obj T'')).map_mul _ _).trans ?_
    exact congrArg (· * e (G.obj T'') (v T' T'' b).val) (he (G.obj T') (G.obj T'') (G.map b) (v T T' a).val)
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip
    (IsClosedImmersion.spec_of_surjective _ hπ)
  haveI : Surjective i := surjective_of_isPullback_sqZero hI hπ hk hpb
  have hbas' : IsBas V' := GlobalTheory.LBObs.isBas_of_preimage_eq X X₀ i C' V' (opOf G) (fun T => hpre _) hbas
  obtain ⟨L, hL, hfrL⟩ := _root_.GlobalTheory.ThinGlue.exists_lb_frame X C' V' hV' u' hbas' hcoc
  have hH : ∀ T, opOf G T ≤ i ⁻¹ᵁ V' ((𝟭 C').obj T) := fun T => (hpre _).ge
  have hfr2 := GlobalTheory.LBObs.isFrame_pull X C' V' hV' L u' X₀ i C' (opOf G) (opOf_le G) (𝟭 C') hH hfrL
  have hueq : (fun T T' (a : T ⟶ T') => res (hH T') (pullU i _ (u' _ _ ((𝟭 C').map a)))) = u := by
    funext T T' a
    ext
    have h2 := hred (G.obj T') (v T T' a).val
    have h3 := hvp T T' a
    refine Eq.trans ?_ (h2.trans h3)
    rfl
  rw [hueq] at hfr2
  exact ⟨L, hL, GlobalTheory.LBObs.lbIso_of_isFrame X₀ C' (opOf G) (opOf_le G) (L.pull i) L₀ u hbas (LB.isLB_pull hL i) hL₀ hfr2 hfr⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensPreimageEqOfSqZeroAugmentationStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_opens_preimage_eq_of_sqZero_augmentation : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ W : X₁.Opens, ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  first | exact @GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | exact GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug | (intros; apply GlobalTheory.LiftSys.exists_opens_preimage_eq_of_sqZero_aug <;> assumption)
end

