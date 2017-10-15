using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms;

namespace Compiler
{
    public partial class Form1 : Form
    {
        public Form1()
        {
            InitializeComponent();
        }

        List<string> Compile( string poly)
        {
            // code: x^23 + 5 * x ^3
            string[] Delimiters = { "+" , "*" , "^" ,"(" , ")"};

            List<string> tokens = new List<string>();

            string temp = "";
            for (int i = 0; i < poly.Length; i++)
            {
                if (poly[i] == '+')
                {
                    tokens.Add(temp);
                    tokens.Add("+");
                    temp = "";
                }
                else if (poly[i] == '*')
                {
                    tokens.Add(temp);
                    tokens.Add("*");
                    temp = "";
                }
                else if(poly[i] == '^')
                {
                    tokens.Add(temp);
                    tokens.Add("^");
                    temp = "";
                }
                else if(poly[i] == '(')
                {
                    tokens.Add(temp);
                    tokens.Add("(");
                    temp = "";
                }
                else if(poly[i] == ')')
                {
                    tokens.Add(temp);
                    tokens.Add(")");
                    temp = "";
                }
                else
                {
                    temp += poly[i];
                }
            }
            if (temp != "")
            {
                tokens.Add(temp);
            }

            return tokens;
        }

        private void btnCompile_Click(object sender, EventArgs e)
        {
             List<string > tokens =  Compile(txtCode.Text);

            for (int i = 0; i < tokens.Count; i++)
            {
                txtTokens.AppendText(tokens[i] + "\n");
            }


        }
    }
}
