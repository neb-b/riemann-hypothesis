module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionTargetGenericCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.ValExt

theorem exists_ext_target : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (y : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y = x ≫ s₀ → ∃ z : Sp V ⟶ M.X, spMap (algebraMap V K) ≫ z = x ≫ t₀ :=
  of_ext GlobalTheory.UPel.HT.ES.IsogDVR.exists_isPIsog_extend_dvr

end GlobalTheory.UPel.HT.ES.ValExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyAtClosedPointOfDvrLimit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.ClosedPtIsog

theorem charP_of_notMem_basicOpen {X : Scheme.{0}} {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (h : Sp k ⟶ X)
    (hz : h (IsLocalRing.closedPoint k) ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) : CharP k p := by
  refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
  by_contra hne
  apply hz
  have hu : IsUnit ((p : ℕ) : Γ(Sp k, h ⁻¹ᵁ ⊤)) := by
    have := (IsUnit.mk0 _ hne).map
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.map (homOfLE (le_top (a := h ⁻¹ᵁ ⊤))).op).hom)
    rwa [map_natCast] at this
  have hm : IsLocalRing.closedPoint k ∈ h ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hu]
    trivial
  exact hm

theorem exists_isPIsog_closedPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ z : M.X, z ∉ M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤)) → {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z} ⊆ {u : M.X | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (ζ υ : Sp k ⟶ M.X) (ou oz : Obj b N (ζ ≫ M.s)) (_ : ObjMap ou M.univ υ) (_ : ObjMap oz M.univ ζ) (ψ : ou.A ⟶ oz.A), υ ≫ M.s = ζ ≫ M.s ∧ IsPIsog c ou oz ψ ∧ ζ (IsLocalRing.closedPoint k) = z ∧ υ (IsLocalRing.closedPoint k) = u} := by
  intro p _ D R _ _ _ _ b N hN hNp _ c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ z hz u hu
  obtain ⟨V, K, _, _, _, _, _, _, y', z', x, hy, hz', hyu, hzz⟩ := hu
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V K
  have hyz : y' ≫ M.s = z' ≫ M.s :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant (Spec.map (CommRingCat.ofHom (Int.castRingHom R))) (specZIsTerminal.hom_ext _ _)
      (spMap (algebraMap V K)) (by rw [reassoc_of% hy, reassoc_of% hz', hst])
  have pull : ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (f : S' ⟶ S) (σ : S' ⟶ Sp R), f ≫ s = σ →
      ∃ o₁ : Obj b N σ, Nonempty (ObjMap o₁ o f) := by
    rintro S S' s o f σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N S S' s f o
  have objMapComp : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
      {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃}
      {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}, ObjMap o₁ o₂ f → ObjMap o₂ o₃ g →
      ObjMap o₁ o₃ (f ≫ g) := by
    intro S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₁ m₂
    exact {
      φ := m₁.φ ≫ m₂.φ
      φ₂ := m₁.φ₂ ≫ m₂.φ₂
      cart := IsGrpPullback.comp m₁.cart m₂.cart
      sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
        by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
      act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
      pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
        (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂)
          (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
          m₂.pol)
      eta := fun y => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  obtain ⟨oV, ⟨mV⟩⟩ := pull M.univ y' (z' ≫ M.s) hyz
  obtain ⟨oV', ⟨mV'⟩⟩ := pull M.univ z' (z' ≫ M.s) rfl
  obtain ⟨oK, ⟨nK⟩⟩ := pull o₀ x _ rfl
  obtain ⟨oK', ⟨nK'⟩⟩ := pull o₀' x _ rfl
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ x o₀ o₀' oK oK' nK nK' ψ₀ hψ
  have m₁ : ObjMap oK M.univ (spMap (algebraMap V K) ≫ y') := hy ▸ objMapComp nK ms₀
  have m₁' : ObjMap oK' M.univ (spMap (algebraMap V K) ≫ z') := hz' ▸ objMapComp nK' mt₀
  obtain ⟨n₁, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁ mV
  obtain ⟨n₁', -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m₁' mV'
  obtain ⟨e, he⟩ := hψ.exists_eq_pow
  have hdom : IsDominant (spMap (algebraMap V K)) := inferInstance
  obtain ⟨ψV, hψV, -⟩ := PIsogExt.exists_isPIsog_extend p D R b N hN hNp 0 c
    ⟨e, he, fun h => absurd h (lt_irrefl 0)⟩ _ _ (spMap (algebraMap V K)) _ (z' ≫ M.s)
    (GlobalTheory.isOpenImmersion_spMap_of_isDiscreteValuationRing V K) hdom inferInstance
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).2)
    (fun y => (GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_Sp V y).1) oV oV' oK oK' n₁ n₁' ψK hψK
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let φ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  let g : Sp k ⟶ Sp V := spMap φ
  have hg : g (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint φ
  have hζ : (g ≫ z') (IsLocalRing.closedPoint k) = z :=
    (Scheme.Hom.comp_apply g z' _).trans ((congrArg z' hg).trans hzz)
  have hυ : (g ≫ y') (IsLocalRing.closedPoint k) = u :=
    (Scheme.Hom.comp_apply g y' _).trans ((congrArg y' hg).trans hyu)
  obtain ⟨ou, ⟨nu⟩⟩ := pull oV g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨oz, ⟨nz⟩⟩ := pull oV' g ((g ≫ z') ≫ M.s) (Category.assoc _ _ _).symm
  obtain ⟨ψk, hψk, -⟩ := ValExt.isPIsog_pull p D R b N c _ _ _ _ g oV oV' ou oz nu nz ψV hψV
  exact ⟨k, inferInstance, inferInstance, charP_of_notMem_basicOpen Fact.out (g ≫ z') (hζ ▸ hz), g ≫ z', g ≫ y', ou, oz,
    objMapComp nu mV, objMapComp nz mV', ψk,
    by rw [Category.assoc, Category.assoc, hyz], hψk, hζ, hυ⟩

end GlobalTheory.UPel.HT.ES.ClosedPtIsog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPIsogenyTargetOfDvrSpecialisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem exists_geomPt_closedPoint (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (y : Sp V ⟶ X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : X.residueField (y (IsLocalRing.closedPoint V)) →+* k)
      (π : Sp k ⟶ Sp V), π ≫ y = spMap σ ≫ X.fromSpecResidueField (y (IsLocalRing.closedPoint V)) ∧
      ∀ q, π q = IsLocalRing.closedPoint V := by
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let g₀ : V →+* k := (algebraMap (IsLocalRing.ResidueField V) k).comp (IsLocalRing.residue V)
  haveI : IsLocalHom g₀ := RingHom.isLocalHom_comp _ _
  have hπ : ∀ q, spMap g₀ q = IsLocalRing.closedPoint V := by
    intro q
    have hq : q = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [hq]
    exact IsLocalRing.comap_closedPoint g₀
  obtain ⟨⟨x, σ⟩, h⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective (spMap g₀ ≫ y)
  rw [Scheme.SpecToEquivOfField_symm_apply] at h
  have hx : x = y (IsLocalRing.closedPoint V) := by
    let q : Sp k := IsLocalRing.closedPoint k
    have e : (Spec.map σ ≫ X.fromSpecResidueField x) q = (spMap g₀ ≫ y) q := congrArg (fun g : Sp k ⟶ X => g q) h
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hπ, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hx
  exact ⟨k, inferInstance, inferInstance, σ.hom, spMap g₀, h.symm, hπ⟩

theorem exists_isogTarget_of_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → IsPIsog c o₀ o₀' ψ₀ → ∀ u : M.X, ∀ z ∈ {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}, ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (σ : M.X.residueField u →+* k) (ζ : Sp k ⟶ M.X), (∀ q, ζ q = z) ∧ CorrQF.IsogTarget M c (spMap σ ≫ M.X.fromSpecResidueField u) ζ := by
  rintro p _ D R _ b N hN hNp c M Y₀ s₀ t₀ o₀ o₀' ms₀ mt₀ ψ₀ hst hψ u z ⟨V, K, _, _, _, _, _, _, y, z', x, hxy, hxz, rfl, rfl⟩
  let eK : K →+* FractionRing V := (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).toRingEquiv.toRingHom
  have heK : eK.comp (algebraMap V K) = algebraMap V (FractionRing V) := by
    ext a; exact (IsLocalization.algEquiv (nonZeroDivisors V) K (FractionRing V)).commutes a
  let kF : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let x' : Sp (FractionRing V) ⟶ Y₀ := spMap eK ≫ x
  have hk : kF = spMap eK ≫ spMap (algebraMap V K) := by
    simp only [kF, spMap, ← heK, CommRingCat.ofHom_comp, Spec.map_comp]
  have hxy' : kF ≫ y = x' ≫ s₀ := by rw [hk, Category.assoc, hxy]; rfl
  have hxz' : kF ≫ z' = x' ≫ t₀ := by rw [hk, Category.assoc, hxz]; rfl
  obtain ⟨o, ⟨my⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N M.X (Sp V) M.s y M.univ
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp (FractionRing V)) (y ≫ M.s) kF o
  have m1 : ObjMap oK M.univ (x' ≫ s₀) := hxy' ▸ GlobalTheory.UPel.HT.ObjMapComp.comp mK my
  obtain ⟨n₀, -⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ m1 ms₀
  have key : ∀ σ : Sp (FractionRing V) ⟶ Sp R, x' ≫ (s₀ ≫ M.s) = σ →
      ∃ o' : Obj b N σ, Nonempty (ObjMap o' o₀' x') := by
    rintro σ rfl
    exact GlobalTheory.HTPull.exists_objMap_pull p D R b N Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) x' o₀'
  obtain ⟨oK', ⟨n₀'⟩⟩ := key (kF ≫ (y ≫ M.s)) (by rw [← Category.assoc, ← hxy', Category.assoc])
  obtain ⟨ψK, hψK, -⟩ := ValExt.isPIsog_pull p D R b N c Y₀ (Sp (FractionRing V)) (s₀ ≫ M.s) (kF ≫ (y ≫ M.s)) x'
    o₀ o₀' oK oK' n₀ n₀' ψ₀ hψ
  obtain ⟨o', m', ψ, hψV, -⟩ := IsogDVR.exists_isPIsog_extend_dvr p D R b N hN hNp c V (y ≫ M.s) o oK oK' mK ψK hψK
  obtain ⟨z, ⟨hz, ⟨mz⟩⟩, -⟩ := M.rep (Sp V) (y ≫ M.s) o'
  obtain ⟨f, -, huniq⟩ := M.rep (Sp (FractionRing V)) (kF ≫ (y ≫ M.s)) oK'
  have e1 := huniq (kF ≫ z) ⟨by rw [Category.assoc, hz], ⟨GlobalTheory.UPel.HT.ObjMapComp.comp m' mz⟩⟩
  have e2 := huniq (x' ≫ t₀) ⟨by rw [Category.assoc, ← hst, ← Category.assoc, ← hxy', Category.assoc],
    ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n₀' mt₀⟩⟩
  haveI : IsSeparated M.s := by
    obtain ⟨n, i, hi, -, e⟩ := M.qproj
    have : IsSeparated (PSpace.str R n) := by
      unfold PSpace.str
      infer_instance
    rw [← e]
    infer_instance
  haveI : M.X.IsSeparated := ⟨by rw [← terminal.comp_from M.s]; infer_instance⟩
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsDominant kF := inferInstanceAs (IsDominant (spMap (algebraMap V (FractionRing V))))
  have hzz : z = z' := ext_of_isDominant kF (by rw [e1, ← e2, hxz'])
  subst hzz
  obtain ⟨k, _, _, σ, π, hπ, hπc⟩ := exists_geomPt_closedPoint V M.X y
  refine ⟨k, inferInstance, inferInstance, σ, π ≫ z, fun q => by rw [Scheme.Hom.comp_apply, hπc], ?_⟩
  rw [← hπ]
  obtain ⟨o₁, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o
  obtain ⟨o₁', ⟨n'⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N (Sp V) (Sp k) (y ≫ M.s) π o'
  obtain ⟨ψ₁, hψ₁, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp V) (Sp k) (y ≫ M.s) (π ≫ (y ≫ M.s)) π
    o o' o₁ o₁' n n' ψ hψV
  refine ⟨by rw [Category.assoc, Category.assoc, hz], ?_⟩
  rw [Category.assoc]
  exact ⟨o₁, o₁', ψ₁, ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n my⟩, ⟨GlobalTheory.UPel.HT.ObjMapComp.comp n' mz⟩, hψ₁⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.ES.CorrQF

theorem charP_of_residueField_of_notMem_basicOpen (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (u : X)
    (hu : u ∉ X.basicOpen ((p : ℕ) : Γ(X, ⊤))) (L : Type) [Field L] (h : X.residueField u →+* L) : CharP L p := by
  have h1 : ¬ IsUnit (X.presheaf.germ ⊤ u trivial ((p : ℕ) : Γ(X, ⊤))) :=
    fun hh => hu ((X.mem_basicOpen ((p : ℕ) : Γ(X, ⊤)) u (Set.mem_univ u)).2 hh)
  rw [map_natCast] at h1
  have h2 : IsLocalRing.residue (X.presheaf.stalk u) ((p : ℕ) : X.presheaf.stalk u) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h1)
  rw [map_natCast] at h2
  have h3 : ((p : ℕ) : L) = 0 := by
    rw [← map_natCast h]
    exact (congrArg h h2).trans (map_zero h)
  exact (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h3

theorem finite_isogTarget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (M : Model b N) (u : M.X), u ∉ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → ∀ (L : Type) [Field L] [IsAlgClosed L] (h : M.X.residueField u →+* L), {ζ : Sp L ⟶ M.X | CorrQF.IsogTarget M c (spMap h ≫ M.X.fromSpecResidueField u) ζ}.Finite := by
  intro p _ D R _ b N hN hNp hm c M u hu L _ _ h
  haveI : CharP L p := charP_of_residueField_of_notMem_basicOpen p M.X u hu L h
  set ξ := spMap h ≫ M.X.fromSpecResidueField u with hξ
  obtain ⟨o₀, ⟨m₀⟩⟩ := HTPull.exists_objMap_pull p D R b N M.X (Sp L) M.s ξ M.univ
  have hF := T.finite_kernels_pIsogenies_harrisTaylor_charP p D R b N hN hNp hm c L (ξ ≫ M.s) o₀
  let Rel : (Sp L ⟶ M.X) → ((T : Over (Sp L)) → (T ⟶ o₀.A) → Prop) → Prop := fun ζ P =>
    ∃ (o' : Obj b N (ξ ≫ M.s)) (ψ₀ : o₀.A ⟶ o'.A), IsPIsog c o₀ o' ψ₀ ∧
      (P = fun T x => x ≫ ψ₀ = 1) ∧ Nonempty (ObjMap o' M.univ ζ) ∧ ζ ≫ M.s = ξ ≫ M.s
  have hsub : ∀ P, {ζ | Rel ζ P}.Subsingleton := by
    rintro P ζ₁ ⟨o₁, ψ₁, hψ₁, rfl, ⟨n₁⟩, hs₁⟩ ζ₂ ⟨o₂, ψ₂, hψ₂, he, ⟨n₂⟩, hs₂⟩
    obtain ⟨m, -⟩ := KerDet.exists_objMap_of_ker_eq p D R b N hN hNp c (Sp L) (ξ ≫ M.s) o₀ o₁ o₂ ψ₁ ψ₂
      hψ₁ hψ₂ (fun T x => Iff.of_eq (congrFun (congrFun he T) x))
    have hn : Nonempty (ObjMap o₁ M.univ ζ₂) := by
      simpa only [Category.id_comp] using (show Nonempty (ObjMap o₁ M.univ (𝟙 (Sp L) ≫ ζ₂)) from ⟨m.comp n₂⟩)
    exact (M.rep (Sp L) (ξ ≫ M.s) o₁).unique ⟨hs₁, ⟨n₁⟩⟩ ⟨hs₂, hn⟩
  refine (hF.biUnion fun P _ => (hsub P).finite).subset ?_
  intro ζ hζ
  obtain ⟨hs, o, o', ψ, ⟨mo⟩, ⟨mo'⟩, hψ⟩ := hζ
  obtain ⟨i₀, -⟩ := IwLevel.exists_objMap_cancel (f := 𝟙 (Sp L)) (g := ξ)
    (cast (congrArg (ObjMap o₀ M.univ) (Category.id_comp ξ).symm) m₀) mo
  obtain ⟨i₁, -⟩ := IwLevel.exists_objMap_cancel (f := 𝟙 (Sp L)) (g := ζ)
    (cast (congrArg (ObjMap o' M.univ) (Category.id_comp ζ).symm) mo') mo'
  obtain ⟨ψ₀, hψ₀, -⟩ := ValExt.isPIsog_pull p D R b N c (Sp L) (Sp L) (ξ ≫ M.s) (ξ ≫ M.s) (𝟙 _)
    o o' o₀ o' i₀ i₁ ψ hψ
  exact Set.mem_biUnion (x := fun T x => x ≫ ψ₀ = 1) ⟨o', ψ₀, hψ₀, rfl⟩ ⟨o', ψ₀, hψ₀, rfl, ⟨mo'⟩, hs.symm⟩

end GlobalTheory.UPel.HT.ES.CorrQF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPIsogenyTargetOfPointPairFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPIsogenyTargetOfPointPair_field_extension : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (c : ℕ) (k L : Type) [Field k] [Field L] (j : k →+* L) (ξ ζ : Sp k ⟶ M.X), CorrQF.IsogTarget M c ξ ζ → CorrQF.IsogTarget M c (spMap j ≫ ξ) (spMap j ≫ ζ) := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap) | (exact GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.isogTarget_spMap  <;> assumption)
end

