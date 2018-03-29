s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T43-[8,6,7]-8-611-71-g2";
s`BelyiDBFilename := "8T43-[8,6,7]-8-611-71-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 6, 7 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 4, 8, 7, 2, 5, 1, 6 ],
[ 3, 7, 5, 1, 2, 6, 4, 8 ],
[ 2, 3, 4, 5, 6, 8, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 3, 7, 5, 1, 2, 6, 4, 8 ],
\[ 2, 3, 4, 5, 6, 8, 7, 1 ]:
 Order := 336 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 3, 7, 5, 1, 2, 6, 4, 8 ],
\[ 2, 3, 4, 5, 6, 8, 7, 1 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 3, 7, 5, 1, 2, 6, 4, 8 ],
\[ 2, 3, 4, 5, 6, 8, 7, 1 ]:
 Order := 336 > |
[ 7, 5, 1, 2, 6, 8, 4, 3 ],
[ 4, 8, 7, 2, 5, 6, 1, 3 ],
[ 8, 1, 2, 3, 4, 5, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 3, 7, 5, 1, 2, 6, 4, 8 ],
\[ 2, 3, 4, 5, 6, 8, 7, 1 ]:
 Order := 336 > |
[ 7, 5, 1, 2, 6, 8, 4, 3 ],
[ 4, 1, 3, 8, 5, 7, 2, 6 ],
[ 3, 1, 4, 6, 7, 5, 2, 8 ]
],
[ PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 3, 7, 5, 1, 2, 6, 4, 8 ],
\[ 2, 3, 4, 5, 6, 8, 7, 1 ]:
 Order := 336 > |
[ 2, 8, 4, 6, 3, 1, 5, 7 ],
[ 1, 5, 3, 7, 4, 2, 8, 6 ],
[ 8, 1, 2, 3, 4, 5, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 3, 4, 8, 7, 2, 5, 1, 6 ],
\[ 3, 7, 5, 1, 2, 6, 4, 8 ],
\[ 2, 3, 4, 5, 6, 8, 7, 1 ]:
 Order := 336 > |
[ 2, 8, 4, 6, 3, 1, 5, 7 ],
[ 1, 2, 5, 7, 8, 3, 6, 4 ],
[ 7, 1, 3, 6, 4, 8, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 4, 8, 7, 2, 5, 1, 6 ],
[ 3, 7, 5, 1, 2, 6, 4, 8 ],
[ 2, 3, 4, 5, 6, 8, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 8, 6, 7, 3, 2, 4, 1, 5 ],
[ 1, 7, 5, 4, 6, 8, 3, 2 ],
[ 2, 3, 4, 5, 6, 8, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 6, 1, 5, 3, 7, 4, 8, 2 ],
[ 7, 2, 8, 4, 6, 3, 5, 1 ],
[ 2, 3, 4, 5, 6, 8, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 4, 5, 2, 3, 6, 7, 8, 1 ],
[ 7, 8, 3, 4, 1, 2, 6, 5 ],
[ 2, 3, 4, 5, 6, 8, 7, 1 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
