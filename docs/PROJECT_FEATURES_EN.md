# Eqratech Arabic Diana Project - Detailed Features Description

## Introduction

The Eqratech Arabic Diana Project is an ambitious and advanced project in the field of Arabic Natural Language Processing (NLP), aimed at building a comprehensive system for analyzing and generating Arabic texts with high scientific accuracy, focusing on all levels of the Arabic language from phonetics to rhetoric.

## Goals and Vision

### Strategic Objectives
1. **Build a comprehensive knowledge base** for the Arabic language covering all linguistic levels
2. **Develop AI engines** capable of understanding and generating Arabic texts with precision
3. **Process Quranic texts** in a respectful scientific manner to achieve deeper understanding of Quranic language
4. **Provide practical tools** for researchers and developers in the Arabic language field

### Target Audience
- **Academic researchers** in Arabic language and its sciences
- **Natural language processing developers** for Arabic
- **Teachers and students** in Arabic language specializations
- **AI enthusiasts** and its applications to Arabic language

## Detailed Features

### 1. Phonetic Layer Engines

#### Phonemes Engine
- **Function**: Analyze and process basic Arabic sounds
- **Content**: 
  - 28 original Arabic letters
  - All forms of hamza (ء، أ، إ، ؤ، ئ)
  - Detailed phonetic information (articulation point, characteristics, IPA)
- **Stored Data**:
  - Letter articulation point (deepest throat, middle of tongue, etc.)
  - Phonetic function
  - Unicode and UTF-8 codes
  - International Phonetic Alphabet (IPA) symbols

#### Harakat (Diacritics) Engine
- **Function**: Process grammatical and structural diacritics
- **Types of Harakat**:
  - Basic diacritics: Fatha (َ), Damma (ُ), Kasra (ِ), Sukun (ْ)
  - Tanween: Fathatan (ً), Dammatan (ٌ), Kasratan (ٍ)
  - Shadda (ّ)
  - Madd and Alif Khanjariyya (ٰ)
- **Associated Information**:
  - Grammatical function (accusative, nominative, genitive marker)
  - Morphological function (pattern construction)
  - Semantic function (distinguishing meanings)

### 2. Morphological Layer Engines

#### Verbs Engine
Covers all types of Arabic verbs:
- **Past tense verbs**: Built on fatha generally
- **Present tense verbs**: Inflected (nominative, accusative, jussive)
- **Imperative verbs**: Built on sukun generally
- **Conjugations**: With singular, dual, and plural, masculine and feminine

#### Active Participle Engine
- **Patterns**: فاعل (fa'il), مُفَاعِل (mufa'il), مُفْعِل (muf'il), فَعَّال (fa'al), etc.
- **Examples**: كاتب (writer), قارئ (reader), حافظ (guardian), ذاهب (going), مُعَلِّم (teacher)
- **Functions**: 
  - A noun indicating who performed the action
  - Works like a verb
  - Inflectable according to position

#### Passive Participle Engine
- **Patterns**: مَفْعول (maf'ul), مُفَعَّل (mufa'al), مُسْتَفْعَل (mustaf'al)
- **Examples**: مكتوب (written), مقروء (read), محفوظ (memorized), مُعَلَّم (taught)
- **Functions**: Indicates who the action was performed on

#### Adjective Engine
- **Multiple patterns**: فَعِل (fa'il), فَعْلان (fa'lan), أَفْعَل (af'al), فَعُول (fa'ul), etc.
- **Examples**: كريم (generous), جميل (beautiful), عظيم (great), طويل (tall), قصير (short)
- **Characteristics**: Indicates a permanent quality in the described

#### Superlative Engine
- **Pattern**: أَفْعَل (af'al) for masculine, فُعْلَى (fu'la) for feminine
- **Examples**: أكبر (bigger/biggest), أصغر (smaller/smallest), أعظم (greater/greatest), أجمل (more/most beautiful)
- **Uses**: Comparison between things

#### Special Pattern Engines
- **Instrumental noun**: مِفْعَال (mif'al), مِفْعَل (mif'al), مِفْعَلَة (mif'ala) - e.g., مِفتاح (key), مِبرَد (file), مِكنَسة (broom)
- **Noun of manner**: فِعْلَة (fi'la) - e.g., جِلسة (session), قِعدة (sitting)
- **Noun of instance**: فَعْلَة (fa'la) - e.g., ضَربة (strike), أكلة (meal)
- **Industrial masdar**: By adding nisba ya and ta - e.g., إنسانية (humanity), عربية (Arabism)

#### Diminutive Engine
- **Patterns**: فُعَيْل (fu'ayl), فُعَيْعِل (fu'ayi'il), فُعَيْعيل (fu'ayil)
- **Function**: Diminution, endearment, or deprecation
- **Examples**: كُتَيِّب (booklet), دُرَيْهِم (small dirham), عُصَيْفُور (little bird)

#### Nisba (Attribution) Engine
- **Form**: Adding doubled nisba ya
- **Examples**: مِصري (Egyptian), دمشقي (Damascene), عربي (Arabic), إسلامي (Islamic)
- **Function**: Attributing something to its origin or place

### 3. Syntactic Layer Engines

#### Nominative Case Engines
1. **Agent (Subject) Engine**:
   - Apparent agent (محمد كتب الدرس - Muhammad wrote the lesson)
   - Implicit agent (كتب الدرس - [He] wrote the lesson)
   - Feminine agent (فاطمة كتبت - Fatima wrote)

2. **Mubtada and Khabar (Subject-Predicate) Engine**:
   - Mubtada and singular khabar (الطالب مجتهد - The student is diligent)
   - Sentence khabar (الطالب يدرس - The student studies)
   - Semi-sentence khabar (الطالب في الفصل - The student is in the class)

#### Accusative Case Engines
1. **Direct Object Engine**: 
   - Explicit direct object (أكلت التفاحة - I ate the apple)
   - Pronoun direct object (أكلتها - I ate it)

2. **Absolute Object Engine**:
   - For emphasis (ضربت ضرباً - I hit [with a] hitting)
   - To show type (ضربت ضرب المعلم - I hit like a teacher's hitting)
   - To show number (ضربت ضربتين - I hit twice)

3. **Object of Purpose Engine**:
   - Shows reason for action (قمت إجلالاً للضيف - I stood up out of respect for the guest)

4. **Haal (Circumstantial) Engine**:
   - Single haal (جاء محمد مسرعاً - Muhammad came hurriedly)
   - Sentence haal (جاء محمد يركض - Muhammad came running)
   - Semi-sentence haal (رأيته على حصانه - I saw him on his horse)

5. **Tamyeez (Specification) Engine**:
   - Specification of essence (طاب محمد نفساً - Muhammad became pleasant in spirit)
   - Specification of ratio (اشتريت رطلاً تمراً - I bought a pound of dates)

#### Passive Voice Engines
1. **Passive Voice Construction Engine**:
   - Converting verb to passive
   - Changing diacritics

2. **Deputy Agent Engine**:
   - Takes place of deleted agent
   - Takes agent's rules

#### Building (Indeclinable) Engine
- Indeclinable nouns (هذا، هؤلاء، أين، كيف - this, these, where, how)
- Indeclinable verbs (past, imperative)
- Particles (all indeclinable)

### 4. Pronoun and Demonstrative Engines

#### Demonstratives Engine
Covers all Arabic demonstratives:
- **For near**: هذا، هذه، هذان، هاتان، هؤلاء (this/these - masculine/feminine/dual/plural)
- **For far**: ذلك، تلك، ذانك، تانك، أولئك (that/those - masculine/feminine/dual/plural)
- **For place**: هنا، هناك، هنالك (here, there)
- **Grammatical functions**: Inflected according to position in sentence

#### Pronouns Engine
- **Detached pronouns**: أنا، أنت، هو، هي، نحن، أنتم، هم (I, you, he, she, we, you [plural], they)
- **Attached pronouns**: 
  - With verbs (كتبتُ، كتبتَ، كتبَ - I wrote, you wrote, he wrote)
  - With nouns (كتابي، كتابك، كتابه - my book, your book, his book)
  - With particles (إني، إنك، إنه - indeed I, indeed you, indeed he)

### 5. Proper Nouns and Names Engines

#### Personal Names Engine
- Names of prophets and companions
- Traditional Arabic names
- Modern names
- **Characteristics**: Diptote or triptote

#### Place Names Engine
- Arab country names
- Historical city names
- Mountain and river names
- **Characteristics**: Most are diptote

#### Names of Allah Engine
- **99 names** of Allah
- **Compound names**: Abd al-Rahman, Abdullah, Abd al-Aziz (Servant of the Merciful, Servant of Allah, Servant of the Mighty)
- **Function**: Sacred names with specific usage

#### Number Names Engine
- Single numbers (واحد، اثنان، ثلاثة، ... - one, two, three, ...)
- Compound numbers (أحد عشر، اثنا عشر، ... - eleven, twelve, ...)
- Coordinated numbers (واحد وعشرون، ... - twenty-one, ...)
- **Complex rules**: Gender agreement, specification

### 6. Rhetorical Engines

#### Simile (Tashbih) Engine
Analyzes and generates simile styles:
- **Complete simile**: Has four elements (compared, compared to, simile tool, aspect of similarity)
- **Eloquent simile**: Omitting tool and aspect
- **Examples**: محمد كالأسد في الشجاعة (Muhammad is like a lion in courage)

#### Metaphor (Isti'ara) Engine
- **Explicit metaphor**: Deleting the compared
- **Implicit metaphor**: Deleting the compared to
- **Examples**: رأيت أسداً يخطب (I saw a lion giving a speech - lion = brave man)

#### Metonymy (Kinaya) Engine
- Expression intended for a meaning other than the apparent
- **Examples**: فلان كثير الرماد (So-and-so has much ash - metonymy for generosity)

#### Paronomasia (Jinas) Engine
- **Perfect paronomasia**: Complete similarity in letters with different meaning
- **Imperfect paronomasia**: Difference in one or more letters
- **Examples**: الصيف صيف، والشتاء شتاء (Summer is summer, and winter is winter)

#### Antithesis (Tibaq) Engine
- Combining opposites in a sentence
- **Examples**: الليل والنهار، الحي والميت، الحلو والمر (Night and day, living and dead, sweet and bitter)

#### Parallelism (Muqabala) Engine
- Bringing two or more compatible meanings, then bringing their opposites
- **Examples**: يحيي ويميت، يعطي ويمنع (He gives life and death, He gives and withholds)

#### Rhymed Prose (Saj') Engine
- Correspondence of endings in the same letter
- **Examples**: الصوم جُنة، والصدقة بُرهان (Fasting is a shield, and charity is proof)

#### Restriction (Qasr) Engine
- Specifying something to something by a special method
- **Methods**: By negation and exception, by innama, by fronting and backing

#### Brevity and Verbosity Engine
- **Brevity**: Expressing much meaning with few words
- **Verbosity**: Increasing words over meaning for a benefit

### 7. Special Construction Engines

#### Interrogative Engine
Handles all interrogative tools:
- **Hamza**: For conceptual or affirmative interrogation
- **Hal**: For affirmation only
- **Man**: For rational beings
- **Ma, Madha**: For irrational things
- **Mata, Ayna, Kayfa, Limadha, Kam**: For time, place, manner, reason, and number

#### Negation Engine
Various negation tools:
- **Ma, La, Lam, Lan**: Basic negation tools
- **Laysa**: Negation verb
- **La nafiya lil-jins**: Works like inna

#### Exclamation (Ta'ajjub) Engine
Exclamation styles:
- **Ma af'alahu**: ما أجملَ السماءَ! (How beautiful is the sky!)
- **Af'il bihi**: أجمِل بالسماءِ! (How beautiful is the sky!)

#### Five Verbs Engine
- Verbs connected with alif al-ithnayn, waw al-jama'a, or ya al-mukhatabah
- **Special inflection**: Raised with proven nun, accusative and jussive with its deletion

### 8. Sentence Generators

#### Simple Generator
- Generates simple sentences using one or two engines
- **Usage**: For quick tests and initial experiments

#### Comprehensive Generator
- Uses all 68+ engines
- Generates up to 5000 diverse sentences
- **Features**:
  - Variety of grammatical structures
  - Combining multiple elements
  - Automatic exclusion of incorrect structures

#### Enhanced Generator
- Smart rules for excluding erroneous structures
- Improving quality of generated sentences
- Integrating rhetoric with grammar

#### Static Generator
- Pre-prepared fixed sentences
- **Usage**: For systematic tests and comparisons

### 9. Quran Processing

#### Data Preparation
- **Normalization**: Standardizing Quranic text
- **Division**: 
  - Training data: ~5000 verses
  - Validation data: ~600 verses
  - Test data: ~600 verses
- **Format**: JSONL files for Transformer model compatibility

#### Transformer Training
- Using modern Transformer models
- Training on Google Colab
- **Objectives**:
  - Understanding Quranic language
  - Predicting diacritics
  - Grammatical and morphological analysis

#### Colab Workflow
- Ready-to-run Jupyter notebook
- Automatic steps:
  1. Clone project
  2. Install requirements
  3. Load data
  4. Start training
  5. Save trained model

### 10. Web Server

#### FastAPI Application
- **Technology**: FastAPI (modern, fast Python framework)
- **Features**:
  - RESTful API
  - Automatic documentation (Swagger UI)
  - Async/await support
  - High performance

#### Endpoints
- `/api/analyze`: Analyze Arabic text
- `/api/generate`: Generate sentences
- `/api/classify`: Grammatical classification
- `/api/engines`: Get list of engines

#### Auto-reload
- Development mode with automatic change monitoring
- Instant code updates without restart

### 11. Export and Data

#### Comprehensive Excel Export
- File `full_multilayer_grammar.xlsx`
- **Content**: 68+ worksheets
- **Each sheet contains**:
  - Linguistic tools
  - Templates and structures
  - Phonemes and diacritics
  - Grammatical, morphological, and semantic functions
  - Examples and notes

#### Specialized CSV Files
- **Phonemes.csv**: Complete phonemes database
- **Harakat.csv**: Diacritics database
- **broken_plurals.csv**: Broken plurals (more than 1000)
- Other specialized files for each grammatical category

### 12. Comparison and Analysis Tools

#### Engine Comparison
- Generate comprehensive comparison reports
- **Criteria**:
  - Number of elements in each engine
  - Diversity and comprehensiveness
  - Compliance with linguistic standards

#### Phoneme Comparison
- Verify phonetic data accuracy
- Match Unicode and UTF-8
- Ensure data completeness

### 13. Reconstruction Tools

#### Reconstruction Utils
Helper functions for data processing:
- Convert diacritic names to symbols
- Analyze Arabic texts
- Extract phonemes and diacritics
- Build complete DataFrame from basic data

## Technologies Used

### Programming Languages and Libraries
- **Python 3.8+**: Main programming language
- **pandas**: Tabular data processing
- **openpyxl**: Read and write Excel files
- **FastAPI**: Build web server
- **uvicorn**: ASGI server for applications
- **pytest**: Testing

### Data Standards
- **UTF-8**: Encoding all Arabic texts
- **Unicode**: International character standard
- **JSONL**: Training data format
- **Excel XLSX**: Final export format

## Statistics and Numbers

### Project Size
- **68+ specialized grammar engines**
- **~5,500 lines of code** in main files
- **20+ CSV files** for basic data
- **6,236 Quranic verses** in training data
- **1000+ broken plurals** in database

### Comprehensiveness
- **Complete** coverage of basic Arabic grammar
- **Extensive** coverage of Arabic morphology
- **Good** coverage of Arabic rhetoric
- **Special** support for Quranic texts

## Potential Uses

### For Researchers
- Study linguistic phenomena in Arabic texts
- Statistical analysis of grammatical structures
- Comparison of rhetorical styles

### For Developers
- Build grammar checking applications
- Develop machine translation systems
- Create Arabic voice assistants

### For Teachers and Students
- Interactive educational tool
- Comprehensive reference for rules
- Automatic example generator

### For Commercial Applications
- Arabic search engines
- Sentiment analysis in texts
- Automatic content generation

## Future Development

### Planned
- Add more grammar engines
- Improve sentence generation accuracy
- Support different Arabic dialects
- Graphical User Interface (GUI)
- Complete web application
- Multilingual support (Arabic-English)

### Future Ideas
- Integration with speech recognition systems
- Mobile app for Android & iOS
- Cloud API for public use
- Advanced deep learning models

## Conclusion

The Eqratech Arabic Diana Project is an ambitious and comprehensive project aimed at serving the Arabic language and its sciences through employing the latest artificial intelligence and natural language processing technologies. The project provides powerful and flexible tools for researchers, developers, and teachers, with a focus on scientific accuracy and comprehensiveness.

The project is open for continuous development and improvement, and we welcome all contributions that help achieve its noble goals in serving the Arabic language.

---
**Last Updated**: December 24, 2025
**Version**: 1.0
**Author**: Eqratech Arabic Project Team
