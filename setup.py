"""
Eqratech Arabic Diana Project
مشروع إقرأتك للعربية - ديانا

A comprehensive Arabic NLP project with grammar analysis and formal verification.
"""

from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

with open("requirements.txt", "r", encoding="utf-8") as fh:
    requirements = [line.strip() for line in fh if line.strip() and not line.startswith("#")]

setup(
    name="eqratech-arabic-diana",
    version="1.0.0",
    author="Eqratech",
    author_email="info@eqratech.com",
    description="Arabic NLP Project with grammar analysis and formal verification",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/sonaiso/Eqratech_Arabic_Diana_Project",
    packages=find_packages(),
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: MIT License",
        "Natural Language :: Arabic",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.8",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Topic :: Scientific/Engineering :: Artificial Intelligence",
        "Topic :: Text Processing :: Linguistic",
    ],
    python_requires=">=3.8",
    install_requires=requirements,
    extras_require={
        "dev": [
            "pytest>=7.0.0",
            "pytest-cov>=4.0.0",
            "black>=23.0.0",
            "flake8>=6.0.0",
        ],
    },
    keywords=[
        "arabic",
        "nlp",
        "natural-language-processing",
        "grammar",
        "morphology",
        "linguistics",
        "formal-verification",
        "coq",
    ],
    project_urls={
        "Bug Reports": "https://github.com/sonaiso/Eqratech_Arabic_Diana_Project/issues",
        "Source": "https://github.com/sonaiso/Eqratech_Arabic_Diana_Project",
    },
)
