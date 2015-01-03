#include<iostream>
#include<fstream>
#include<vector>
#include<string>

using namespace std;

string ParseData(vector<string> &Clauses);
void ReduceClause(vector<string> &Clauses);
void Resolution(vector<string>&Clauses, vector<string> &JClauses, vector<string> &UClauses, vector<string> &NotJClauses, string &variables);
bool FindReduction(string clause, string vars);
void ReduceUClause(vector<string> &Clauses,char var);

int main()
{
   vector<string> Clauses;
   vector<string> JClauses;
   vector<string> UClauses;
   vector<string> NotJClause;
   int rounds;

   string variables;

   variables = ParseData(Clauses);
   rounds = variables.size();
   for(int i = 0; i < rounds; i++)
   {
      Resolution(Clauses, JClauses, UClauses, NotJClause, variables);
   }

   if(Clauses.empty())
      cout << "Satisfiable" << endl;
   else
      cout << "Not Satisfiable" << endl;
   return 0;
}
string ParseData(vector<string> &Clauses)
{
   ifstream ReadIn;
   string StringIn;
   string SingleClause;
   string Variables;
   char CharIn;
   int cnt;
   ReadIn.open("formula.txt");

   if(ReadIn.fail())
   {
      cout << "Error Reading the file!" << endl;
   }
   else
   {
      ReadIn >> CharIn;
      while(!ReadIn.eof())
      {
         if(isalpha(CharIn))
         {
            if(Variables.find(CharIn) == -1)
            {
               Variables = Variables + CharIn;
            }
         }
         if(CharIn != '&' && CharIn != '(' && CharIn != ')' && CharIn !='|')
         {
            StringIn = StringIn + CharIn;
         }
         else if (CharIn == '&')
         {
            Clauses.push_back(StringIn);
            StringIn.clear();
         }

         ReadIn >> CharIn;
      }
      Clauses.push_back(StringIn);
   }
   return Variables;
}
void Resolution(vector<string>&Clauses, vector<string> &JClauses, vector<string> &UClauses,vector<string> &NotJClauses, string &variables)
{
   string clause;

   bool reduce;
   bool reduce2 = false;
   int cnt = 0;
   int cnt2;
   int cnt3;
   int index;
   bool satisfiable = false;
   bool flag1 = false;
   string tempClause;
   //Determine if any of the clauses have a variable x and -x and reduce clauses if need be
   for(int i = 0; i < Clauses.size(); i++)
   {
      reduce = FindReduction(Clauses[i], variables);
      if(reduce == true)
      {
         Clauses[i] = "0";
         reduce2 = true;
      }
   }
   if(reduce2)
      ReduceClause(Clauses);


   //Produce  a set of clauses with respect to vars in
   for(int i = 0; i < Clauses.size(); i++)
   {
      if(Clauses[i].find(variables[cnt]) != -1)
         JClauses.push_back(Clauses[i]);
      else
         NotJClauses.push_back(Clauses[i]);
   }


   //Create set of U Clauses
   cnt3 = 0;
   cnt2 = 0;
   if(JClauses.size() > 0)
   {
      for(int i = 0; i < JClauses.size() - 1; i++)
      {
         cnt2 = cnt3;
         index = JClauses[i].find(variables[cnt]);
         tempClause = JClauses[i];

         if(index != 0 && tempClause[index-1] == '-')
            flag1 = true;
         else
            flag1 = false;

         while(cnt2 < JClauses.size() - 1)
         {
            if(flag1)
            {
               index = JClauses[cnt2+1].find(variables[cnt]);
               tempClause = JClauses[cnt2+1];

               if(index == 0 || tempClause[index-1] != '-')
               {
                  UClauses.push_back(JClauses[i] + JClauses[cnt2+1]);
               }
            }
            else
            {
               index = JClauses[cnt2+1].find(variables[cnt]);
               tempClause = JClauses[cnt2+1];

               if(index != 0 && tempClause[index - 1] == '-')
               {
                  UClauses.push_back(JClauses[i] + JClauses[cnt2+1]);
               }
            }
            cnt2++;
         }
         cnt3++;
      }
   }
   ReduceUClause(UClauses, variables[cnt]);
   
   //get the next S' set
   Clauses.clear();

   for(int i = 0; i < NotJClauses.size(); i++)
   {
      Clauses.push_back(NotJClauses[i]);
   }
   for(int i = 0; i < UClauses.size(); i++)
   {
      Clauses.push_back(UClauses[i]);
   }
   //clear the sets containing old information
   JClauses.clear();
   NotJClauses.clear();
   UClauses.clear();
   variables.erase(0,1);

}
bool FindReduction(string clause,string vars)
{

   int identifier1 = 0;
   int identifier2 = 0;
   vector<int> indicies;
   bool reduce = false;

   for(int i = 0; i < vars.size() && reduce == false; i++)
   {
      for(int j = 0; j < clause.length();j++)
      {
         if(clause[j] == vars[i])
         {
            indicies.push_back(j);
         }
      }
      if(indicies.size() >=2)
      {
         for(int k = 0; k < indicies.size() && reduce == false; k++)
         {
            if(indicies[k] != 0)
            {
               if(clause[indicies[k]-1] == '-')
                  identifier1 = 1;
               else
                  identifier2 = 1;            
            }
            else
               identifier2 = 1;
            if(identifier1 == 1 && identifier2 == 1)
               reduce = true;
         }
      }
      indicies.clear();
      identifier1 = 0;
      identifier2 = 0;
   }

   return reduce;
}
void ReduceClause(vector<string> &Clauses)
{
   vector<string> newClauses;
   for(int i = 0; i < Clauses.size(); i++)
   {
      if(Clauses[i] != "0")
      {
         newClauses.push_back(Clauses[i]);
      }
   }
   Clauses.clear();

   for(int i = 0; i < newClauses.size(); i++)
   {
      Clauses.push_back(newClauses[i]);
   }

}
void ReduceUClause(vector<string> &Clauses, char var)
{
   string tempClause;
   string tempNewClause;
   int find = 0;
   int cnt = 0;

   for(int i = 0; i < Clauses.size(); i++)
   {
      tempClause = Clauses[i];

      find = tempClause.find(var);
      while(find != -1)
      {
         find = tempClause.find(var);
         tempClause.erase(find,1);

         if( find != 0 && tempClause[find - 1] == '-')
            tempClause.erase(find-1,1);

         find = tempClause.find(var);
      }

      Clauses[i] = tempClause;
   }
}