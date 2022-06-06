#!/bin/bash
echo " [reading]    wysk-syntax.yaml"
echo " [writing]    wysk.tmLanguage.json"
npx js-yaml syntaxes/wysk-syntax.yaml > syntaxes/wysk.tmLanguage.json
echo " [closing]    wysk-syntax.yaml -> wysk.tmLanguage.json"
echo " [copying]    ./* -> ~/.vscode-oss/extensions/wysk-syntax"
cp -r * ~/.vscode-oss/extensions/wysk-syntax
echo " [copying]    ./* -> ~/.vscode/extensions/wysk-syntax"
cp -r * ~/.vscode/extensions/wysk-syntax