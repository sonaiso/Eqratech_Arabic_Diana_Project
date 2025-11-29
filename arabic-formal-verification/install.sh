#!/bin/bash
# ============================================================
# install.sh - SFGCOQ Installation Script
# تثبيت نظام التحقق الرسمي للنحو العربي
# ============================================================

set -e

echo "=============================================="
echo "SFGCOQ - نظام التحقق الرسمي للنحو العربي"
echo "Arabic Grammar Formal Verification System"
echo "=============================================="
echo ""

# Check operating system
OS="$(uname -s)"

install_coq_linux() {
    echo "🐧 Installing COQ on Linux..."
    if command -v apt-get &> /dev/null; then
        sudo apt-get update
        sudo apt-get install -y coq
    elif command -v dnf &> /dev/null; then
        sudo dnf install -y coq
    elif command -v pacman &> /dev/null; then
        sudo pacman -S coq
    else
        echo "❌ Package manager not found. Please install COQ manually."
        echo "   Visit: https://coq.inria.fr/download"
        exit 1
    fi
}

install_coq_macos() {
    echo "🍎 Installing COQ on macOS..."
    if command -v brew &> /dev/null; then
        brew install coq
    else
        echo "❌ Homebrew not found. Please install Homebrew first:"
        echo "   /bin/bash -c \"\$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)\""
        exit 1
    fi
}

install_coq_windows() {
    echo "🪟 Windows detected."
    echo ""
    echo "Please install COQ manually using one of these methods:"
    echo ""
    echo "Option 1: COQ Platform (Recommended)"
    echo "  Download from: https://github.com/coq/platform/releases"
    echo ""
    echo "Option 2: Using Chocolatey"
    echo "  choco install coq"
    echo ""
    echo "Option 3: Using WSL (Windows Subsystem for Linux)"
    echo "  wsl --install"
    echo "  Then run this script inside WSL"
    echo ""
}

check_coq_installed() {
    if command -v coqc &> /dev/null; then
        COQ_VERSION=$(coqc --version | head -n 1)
        echo "✓ COQ is already installed: $COQ_VERSION"
        return 0
    else
        return 1
    fi
}

compile_proofs() {
    echo ""
    echo "🔨 Compiling COQ proofs..."
    cd "$(dirname "$0")/coq"
    
    if make all; then
        echo ""
        echo "✓ All proofs compiled and verified successfully!"
        echo ""
        echo "Files compiled:"
        ls -la *.vo 2>/dev/null || echo "  (no .vo files found)"
    else
        echo "❌ Compilation failed. Please check the error messages above."
        exit 1
    fi
}

print_usage() {
    echo ""
    echo "=============================================="
    echo "Installation Complete!"
    echo "=============================================="
    echo ""
    echo "📁 Project Structure:"
    echo "   coq/"
    echo "   ├── ArabicGrammar.v    - Core grammar definitions"
    echo "   ├── NawasighRules.v    - Kana/Inna sisters rules"
    echo "   ├── MorphologyRules.v  - Morphological rules"
    echo "   └── Makefile           - Build automation"
    echo ""
    echo "🚀 Quick Start:"
    echo "   cd coq"
    echo "   make          # Compile all proofs"
    echo "   make verify   # Verify all proofs"
    echo "   make clean    # Clean compiled files"
    echo ""
    echo "📚 Documentation:"
    echo "   - README.md              - Project documentation"
    echo "   - docs/web/index.html    - Web interface"
    echo ""
    echo "🔗 Resources:"
    echo "   - COQ Documentation: https://coq.inria.fr/documentation"
    echo "   - COQ Tutorials: https://coq.inria.fr/tutorial-nahas"
    echo ""
}

# Main installation flow
main() {
    echo "Checking for COQ installation..."
    echo ""
    
    if check_coq_installed; then
        echo ""
        read -p "Do you want to compile the proofs now? (y/n) " -n 1 -r
        echo ""
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            compile_proofs
        fi
    else
        echo "COQ is not installed."
        echo ""
        
        case "$OS" in
            Linux*)
                read -p "Install COQ now? (y/n) " -n 1 -r
                echo ""
                if [[ $REPLY =~ ^[Yy]$ ]]; then
                    install_coq_linux
                    compile_proofs
                fi
                ;;
            Darwin*)
                read -p "Install COQ now? (y/n) " -n 1 -r
                echo ""
                if [[ $REPLY =~ ^[Yy]$ ]]; then
                    install_coq_macos
                    compile_proofs
                fi
                ;;
            CYGWIN*|MINGW*|MSYS*)
                install_coq_windows
                ;;
            *)
                echo "❌ Unknown operating system: $OS"
                echo "   Please install COQ manually from: https://coq.inria.fr/download"
                exit 1
                ;;
        esac
    fi
    
    print_usage
}

main "$@"
