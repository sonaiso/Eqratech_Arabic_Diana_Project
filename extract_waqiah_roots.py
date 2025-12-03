#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Surah Al-Waqi'ah (The Event) - Pivotal Roots Extraction
Extracts and analyzes the key semantic roots from Surah 56
"""

import re
from collections import Counter
import csv

# Read the entire Quran text
with open('quran-simple-enhanced.txt', 'r', encoding='utf-8') as f:
    quran_text = f.read()

# Extract all verses (each line is a verse, starting from Al-Fatiha)
verses = [line.strip() for line in quran_text.split('\n') if line.strip()]

# Surah Al-Waqi'ah starts at verse 5113 (cumulative count) and has 96 verses
# But we need to count: Al-Fatiha (7) + Al-Baqarah (286) + ... up to Surah 55
# For simplicity, let's search for distinctive words

# Calculate starting position for Surah 56
verse_counts = [7, 286, 200, 176, 120, 165, 206, 75, 129, 109, 123, 111, 43, 52, 99, 128, 111, 110, 98, 135, 112, 78, 118, 64, 77, 227, 93, 88, 69, 60, 34, 30, 73, 54, 45, 83, 182, 88, 75, 85, 54, 53, 89, 59, 37, 35, 38, 29, 18, 45, 60, 49, 62, 55, 78]
# Surah 56 starts after 55 surahs
start_verse = sum(verse_counts)
end_verse = start_verse + 96

print(f"Surah Al-Waqi'ah: verses {start_verse+1} to {end_verse}")
waqiah_verses = verses[start_verse:end_verse]

print(f"Extracted {len(waqiah_verses)} verses")
print("\nFirst 5 verses:")
for i, verse in enumerate(waqiah_verses[:5], 1):
    print(f"{i}. {verse}")

# Key roots in Arabic that appear in Al-Waqi'ah
# We'll search for these root patterns
key_roots = {
    'وقع': ['وَقَعَ', 'الْوَاقِعَ', 'وَاقِعَ'],  # The Event (root: W-Q-ʿ)
    'خفض': ['خَافِضَ', 'خَفْض'],  # Lowering (Kh-F-Ḍ)
    'رفع': ['رَافِعَ', 'رَفْع', 'مَرْفُوع'],  # Raising (R-F-ʿ)
    'رجج': ['رُجَّ', 'رَجّ'],  # Shaking (R-J-J)
    'بسس': ['بُسَّ', 'بَسّ'],  # Crumbling (B-S-S)
    'سبق': ['السَّابِقُونَ', 'سَبَقَ', 'سَابِق'],  # Preceders (S-B-Q)
    'يمن': ['الْيَمِين', 'الْمَيْمَنَة', 'يَمِين'],  # Right side (Y-M-N)
    'شمل': ['الشِّمَال', 'الْمَشْأَمَة', 'شِمَال'],  # Left side (Sh-M-L) 
    'جنن': ['جَنَّة', 'جَنَّات', 'جِنَان'],  # Garden/Paradise (J-N-N)
    'نعم': ['نَعِيم', 'نَاعِم', 'النَّعِيم'],  # Bliss (N-ʿ-M)
    'كرم': ['كَرِيم', 'أَكْرَم', 'الْكَرِيم'],  # Noble/Generous (K-R-M)
    'نزل': ['نَزَّلَ', 'نُزُل', 'نَازِل', 'مُنَزَّل'],  # Descending (N-Z-L)
    'خلق': ['خَلَقَ', 'خَالِق', 'خَلْق'],  # Creation (Kh-L-Q)
    'نشأ': ['أَنشَأَ', 'نَشْأَة', 'نَاشِئ', 'إِنشَاء'],  # Growth/Origin (N-Sh-ʾ)
    'موت': ['الْمَوْت', 'مَيِّت', 'مَاتَ'],  # Death (M-W-T)
    'كذب': ['كَذَّبَ', 'مُكَذِّب', 'تَكْذِيب'],  # Denial (K-Dh-B)
    'قرب': ['قَرِيب', 'مُقَرَّب', 'قُرْب'],  # Near/Close (Q-R-B)
    'روح': ['رَوْح', 'رَيْحَان', 'رُوح'],  # Spirit/Fragrance (R-W-Ḥ)
    'سلم': ['سَلَام', 'مُسَلِّم'],  # Peace (S-L-M)
    'حمم': ['حَمِيم', 'حَامِّ'],  # Boiling (Ḥ-M-M)
    'ظلل': ['ظِلّ', 'ظَلِيل'],  # Shade (Ẓ-L-L)
    'يقن': ['الْيَقِين', 'يَقِن', 'مُوقِن'],  # Certainty (Y-Q-N)
}

# Extract roots and their occurrences
root_analysis = {}
for root, patterns in key_roots.items():
    occurrences = []
    for verse_num, verse in enumerate(waqiah_verses, 1):
        for pattern in patterns:
            if pattern in verse:
                occurrences.append({
                    'verse': verse_num,
                    'pattern': pattern,
                    'text': verse
                })
    if occurrences:
        root_analysis[root] = occurrences

# Generate report
print(f"\n{'='*80}")
print("PIVOTAL ROOTS IN SURAH AL-WAQI'AH")
print(f"{'='*80}\n")

# Sort by frequency
sorted_roots = sorted(root_analysis.items(), key=lambda x: len(x[1]), reverse=True)

total_occurrences = 0
for root, occurrences in sorted_roots:
    count = len(occurrences)
    total_occurrences += count
    print(f"📌 Root: {root}")
    print(f"   Count: {count} occurrence(s)")
    print(f"   Verses: {', '.join(str(o['verse']) for o in occurrences)}")
    print(f"   Forms: {', '.join(set(o['pattern'] for o in occurrences))}")
    print()

print(f"\n{'='*80}")
print(f"TOTAL: {len(root_analysis)} distinct roots, {total_occurrences} total occurrences")
print(f"{'='*80}\n")

# Create CSV output
csv_data = []
for root, occurrences in sorted_roots:
    for occ in occurrences:
        csv_data.append({
            'Root': root,
            'Verse_Number': occ['verse'],
            'Form': occ['pattern'],
            'Verse_Text': occ['text'][:100] + '...' if len(occ['text']) > 100 else occ['text']
        })

# Write to CSV
with open('surah_waqiah_pivotal_roots.csv', 'w', encoding='utf-8', newline='') as f:
    if csv_data:
        writer = csv.DictWriter(f, fieldnames=['Root', 'Verse_Number', 'Form', 'Verse_Text'])
        writer.writeheader()
        writer.writerows(csv_data)

print("✅ Results saved to: surah_waqiah_pivotal_roots.csv")

# Semantic analysis
print("\n" + "="*80)
print("SEMANTIC CATEGORIES")
print("="*80 + "\n")

categories = {
    'The Event & Cosmic Change': ['وقع', 'رجج', 'بسس', 'خفض', 'رفع'],
    'The Three Groups': ['سبق', 'يمن', 'شمل'],
    'Paradise & Bliss': ['جنن', 'نعم', 'ظلل', 'روح'],
    'Creation & Origin': ['خلق', 'نشأ'],
    'Nobility & Honor': ['كرم', 'قرب'],
    'Death & Certainty': ['موت', 'يقن'],
    'Revelation': ['نزل'],
    'Denial': ['كذب'],
    'Peace & Greeting': ['سلم'],
    'Punishment': ['حمم'],
}

for category, roots in categories.items():
    found_roots = [r for r in roots if r in root_analysis]
    if found_roots:
        print(f"🔸 {category}:")
        for root in found_roots:
            count = len(root_analysis[root])
            print(f"   • {root}: {count} occurrence(s)")
        print()

print("\n" + "="*80)
print("ANALYSIS COMPLETE")
print("="*80)
